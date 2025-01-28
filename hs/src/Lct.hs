{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TypeFamilies #-}

-- | Link/cut tree.
module Lct
  ( -- Link/cut tree
    Lct (..),

    -- * Constructors
    new,
    build,
    write,
    modify,
    link,
    cut,
    prodPath,
  )
where

import Control.Monad (unless, when)
import Control.Monad.Primitive (PrimMonad, PrimState, stToPrim)
import Data.Bit
import Data.Bits hiding (rotate)
import Data.Vector.Generic.Mutable qualified as VGM
import Data.Vector.Unboxed qualified as VU
import Data.Vector.Unboxed.Mutable qualified as VUM

-- | Vertex in original grpah.
type Vertex = Int

-- | Index of nodes in a `Lct`.
type IndexLct = Int

{-# INLINE undefLct #-}
undefLct :: IndexLct
undefLct = -1

{-# INLINE nullLct #-}
nullLct :: IndexLct -> Bool
nullLct = (== -1)

-- | Link/cut tree.
data Lct s a = Lct
  { -- | Decomposed node data storage: left children.
    lLct :: !(VUM.MVector s IndexLct),
    -- | Decomposed node data storage: right children.
    rLct :: !(VUM.MVector s IndexLct),
    -- | Decomposed node data storage: parents.
    pLct :: !(VUM.MVector s IndexLct),
    -- | Decomposed node data storage: subtree sizes.
    sLct :: !(VUM.MVector s Int),
    -- | Decomposed node data storage: reverse flag.
    revLct :: !(VUM.MVector s Bit),
    -- | Decomposed node data storage: payloads.
    vLct :: !(VUM.MVector s a),
    -- | Decomposed node data storage: aggregation of payloads.
    aggLct :: !(VUM.MVector s a),
    -- | Decomposed node data storage: path-parent aggregation value. This is required for subtree
    -- folding queries over commutative monoids only.
    midLct :: !(VUM.MVector s a)
  }

-- | \(O(N)\)
{-# INLINE new #-}
new :: (PrimMonad m, Monoid a, VU.Unbox a) => Int -> m (Lct (PrimState m) a)
new n = do
  lLct <- VUM.replicate n undefLct
  rLct <- VUM.replicate n undefLct
  pLct <- VUM.replicate n undefLct
  sLct <- VUM.replicate n 0
  revLct <- VUM.replicate n (Bit False)
  vLct <- VUM.replicate n mempty
  aggLct <- VUM.replicate n mempty
  -- commutative monoid subtree folding queries only
  midLct <- VUM.replicate n mempty
  pure Lct {..}

-- | \(O(N + E \log E)\)
{-# INLINE build #-}
build :: (PrimMonad m, Monoid a, VU.Unbox a) => VU.Vector a -> VU.Vector (Vertex, Vertex) -> m (Lct (PrimState m) a)
build xs es = do
  lct <- do
    let !n = VU.length xs
    lLct <- VUM.replicate n undefLct
    rLct <- VUM.replicate n undefLct
    pLct <- VUM.replicate n undefLct
    sLct <- VUM.replicate n 0
    revLct <- VUM.replicate n (Bit False)
    vLct <- VU.thaw xs
    aggLct <- VUM.replicate n mempty
    midLct <- VUM.replicate n mempty
    pure Lct {..}
  VU.forM_ es $ \(!u, !v) -> do
    link lct u v
  pure lct

-- -------------------------------------------------------------------------------------------------
-- Balancing
-- -------------------------------------------------------------------------------------------------

-- | \(O(1)\) Rotates up a non-root node.
-- {-# INLINE rotate #-} -- コンパイルが長いので INLINE を外す (INLINE を付けると若干速くなる)
rotate :: (PrimMonad m, Monoid a, VU.Unbox a) => Lct (PrimState m) a -> IndexLct -> m ()
rotate lct@Lct {pLct, lLct, rLct} v = stToPrim $ do
  p <- VGM.unsafeRead pLct v
  pp <- VGM.unsafeRead pLct p
  pl <- VGM.unsafeRead lLct p

  c <-
    if pl == v
      then do
        -- rotate right:
        --   p      v  <-- reference from `pp` is updated later
        --  /        \
        -- v    ->    p
        --  \        /
        --   c      c
        c <- VGM.unsafeExchange rLct v p
        VGM.unsafeWrite lLct p c
        pure c
      else do
        -- rotate left:
        -- p          v  <-- reference from `pp` is updated later
        --  \        /
        --   v  ->  p
        --  /        \
        -- c          c
        c <- VGM.unsafeExchange lLct v p
        VGM.unsafeWrite rLct p c
        pure c

  updateNodeLct lct p
  updateNodeLct lct v

  -- update the reference from `pp`:
  unless (nullLct pp) $ do
    ppl <- VGM.unsafeRead lLct pp
    if ppl == p
      then VGM.unsafeWrite lLct pp v
      else do
        ppr <- VGM.unsafeRead rLct pp
        if ppr == p
          then VGM.unsafeWrite rLct pp v
          else do
            -- overwrite the light (path-parent) pointer:
            changeLightLct lct pp p v

  -- update parent pointers to `pp`: pp <-- v <-- p <-- c
  VGM.unsafeWrite pLct v pp
  VGM.unsafeWrite pLct p v
  unless (nullLct c) $ do
    VGM.unsafeWrite pLct c p

-- | Amortized \(O(\log N)\). Moves a node up to the root, performing self-balancing heuristic
-- called rotations.
-- {-# INLINE splay #-} -- コンパイルが長いので INLINE を外す (INLINE を付けると若干速くなる)
splay :: (PrimMonad m, Monoid a, VU.Unbox a) => Lct (PrimState m) a -> IndexLct -> m ()
splay lct@Lct {pLct} c = stToPrim $ do
  pushNode lct c
  let inner = do
        isRootC <- isRootNode lct c
        unless isRootC $ do
          p <- VGM.unsafeRead pLct c
          pp <- if nullLct p then pure undefLct else VGM.unsafeRead pLct p
          placeP <- nodePlace lct p
          if placeP == RootNodeLct
            then do
              pushNode lct p
              pushNode lct c
              rotate lct c
            else do
              placeC <- nodePlace lct c
              pushNode lct pp
              pushNode lct p
              pushNode lct c
              if placeC == placeP
                then do
                  -- Rotate right twice:
                  --
                  --       pp       p         c
                  --      /        / \         \
                  --    p     ->  c   pp  ->    p
                  --   /                         \
                  -- c                            pp

                  -- Or rotate left twice:
                  --
                  --  pp             p            c
                  --   \            / \          /
                  --    p     ->  pp   c  ->    p
                  --     \                     /
                  --      c                   pp

                  rotate lct p
                  rotate lct c
                else do
                  --       pp         pp         c
                  --      /          /          | \
                  --    p     ->   c      ->   p   pp
                  --     \        /
                  --      c      p
                  rotate lct c
                  rotate lct c
          inner
  inner

-- * Node helpers

-- | \(O(1)\)
{-# INLINE isRootNode #-}
isRootNode :: (PrimMonad m) => Lct (PrimState m) a -> IndexLct -> m Bool
isRootNode lct v = do
  (== RootNodeLct) <$> nodePlace lct v

-- TODO: return heavy/light notion
data NodePlaceLct = RootNodeLct | LeftNodeLct | RightNodeLct
  deriving (Eq)

-- | \(O(1)\)
{-# INLINE nodePlace #-}
nodePlace :: (PrimMonad m) => Lct (PrimState m) a -> IndexLct -> m NodePlaceLct
nodePlace Lct {pLct, lLct, rLct} v = do
  p <- VGM.unsafeRead pLct v
  if nullLct p
    then pure RootNodeLct
    else do
      pl <- VGM.unsafeRead lLct p
      if pl == v
        then pure LeftNodeLct
        else do
          pr <- VGM.unsafeRead rLct p
          if pr == v
            then pure RightNodeLct
            else pure RootNodeLct

-- -------------------------------------------------------------------------------------------------
-- Node methods
-- -------------------------------------------------------------------------------------------------

-- | Amortized \(O(\log N)\). Propgates the lazily propagated values on a node.
{-# INLINE pushNode #-}
pushNode :: (PrimMonad m, VU.Unbox a) => Lct (PrimState m) a -> IndexLct -> m ()
pushNode lct@Lct {lLct, rLct, revLct} v = do
  Bit b <- VGM.unsafeExchange revLct v (Bit False)
  when b $ do
    l <- VGM.unsafeRead lLct v
    r <- VGM.unsafeRead rLct v
    unless (nullLct l) $ reverseNode lct l
    unless (nullLct r) $ reverseNode lct r

-- | \(O(1)\)
{-# INLINE reverseNode #-}
reverseNode :: (PrimMonad m, VU.Unbox a) => Lct (PrimState m) a -> IndexLct -> m ()
reverseNode lct@Lct {revLct} i = do
  -- lazily propagate new reverse from the children, or cancel:
  VGM.unsafeModify revLct (xor (Bit True)) i
  -- swap
  swapLrNodeLct lct i

-- | \(O(1)\) Reverses the left and the right children, lazily and recursively.
{-# INLINE swapLrNodeLct #-}
swapLrNodeLct :: (PrimMonad m, VU.Unbox a) => Lct (PrimState m) a -> IndexLct -> m ()
swapLrNodeLct Lct {lLct, rLct} i = do
  -- swap chidlren
  VGM.unsafeModifyM lLct (VGM.unsafeExchange rLct i) i

-- | \(O(1)\) Recomputes the node size and the monoid aggregation.
{-# INLINE updateNodeLct #-}
updateNodeLct :: (PrimMonad m, Monoid a, VU.Unbox a) => Lct (PrimState m) a -> IndexLct -> m ()
updateNodeLct Lct {..} i = do
  l <- VGM.unsafeRead lLct i
  r <- VGM.unsafeRead rLct i
  v <- VGM.unsafeRead vLct i
  m <- VGM.unsafeRead midLct i

  (!size', !agg') <-
    if nullLct l
      then pure (1 :: Int, v)
      else do
        lSize <- VGM.unsafeRead sLct l
        lAgg <- VGM.unsafeRead aggLct l
        pure (lSize + 1, lAgg <> v)

  (!size'', !agg'') <-
    if nullLct r
      then pure (size', agg')
      else do
        rSize <- VGM.unsafeRead sLct r
        rAgg <- VGM.unsafeRead aggLct r
        pure (size' + rSize, agg' <> rAgg)

  VGM.unsafeWrite sLct i size''
  VGM.unsafeWrite aggLct i agg''

-- | \(O(1)\) Called on adding a path-parent edge. This is for subtree folding.
{-# INLINE addLightLct #-}
addLightLct :: (PrimMonad m, Semigroup a, VU.Unbox a) => Lct (PrimState m) a -> IndexLct -> IndexLct -> m ()
addLightLct _ _ _ = do
  pure ()

-- | \(O(1)\) Called on changing a path-parent edge. This is for subtree folding.
{-# INLINE changeLightLct #-}
changeLightLct :: (PrimMonad m) => Lct (PrimState m) a -> IndexLct -> IndexLct -> IndexLct -> m ()
changeLightLct _ _ _  _ = do
  pure ()

-- | \(O(1)\) Called on erasing a path-parent edge. This is for subtree folding.
{-# INLINE eraseLightLct #-}
eraseLightLct :: (PrimMonad m, Semigroup a, VU.Unbox a) => Lct (PrimState m) a -> IndexLct -> IndexLct -> m ()
eraseLightLct _ _ _ = do
  pure ()

-- -------------------------------------------------------------------------------------------------
-- Link/cut operations
-- -------------------------------------------------------------------------------------------------

-- FIXME: isn't it log^2 N?

-- | Amortized \(O(\log N)\). Makes the root of the underlying tree and @v0@ to be in the same
-- preferred path (auxiliary tree). @v0@ will be the root of the auxiliary tree. After the
-- opeartion, all children of @v0@ are detached from the preferred path.
{-# INLINE expose #-}
expose :: (PrimMonad m, Monoid a, VU.Unbox a) => Lct (PrimState m) a -> IndexLct -> m IndexLct
expose lct@Lct {pLct, rLct} v0 = do
  let inner v lastRoot
        | nullLct v = pure lastRoot
        | otherwise = do
            -- go up to the top of the auxiliary tree:
            splay lct v

            -- make @lastRoot@ the right child of @v@:
            --    v               v
            --   /|\        ->   /|\
            --    | r             | lastRoot  <-- @v0@ (in the @lastRoot@) will be connected to the root
            --    lastRoot        r
            r <- VGM.unsafeRead rLct v
            unless (nullLct r) $ addLightLct lct v r
            unless (nullLct lastRoot) $ eraseLightLct lct v lastRoot
            VGM.unsafeWrite rLct v lastRoot
            updateNodeLct lct v

            -- go up to the next auxiliary tree:
            --    p
            --    |
            --    v
            --     \
            --      lastRoot
            vp <- VGM.unsafeRead pLct v
            inner vp v

  res <- inner v0 undefLct
  splay lct v0
  pure res

-- | Amortized \(O(\logN)\). Makes the root and @v0@ to be in the same preferred path (same
-- auxiliary tree).
{-# INLINE expose_ #-}
expose_ :: (PrimMonad m, Monoid a, VU.Unbox a) => Lct (PrimState m) a -> IndexLct -> m ()
expose_ lct v0 = do
  _ <- expose lct v0
  pure ()

-- | Amortized \(O(\log n)\). Makes @v@ a new root of the underlying tree.
{-# INLINE evert #-}
evert :: (PrimMonad m, Monoid a, VU.Unbox a) => Lct (PrimState m) a -> IndexLct -> m ()
evert lct v = do
  -- make @v@ be in the same preferred path as root. note that @v@ is at the root of the auxiliary tree.
  expose_ lct v
  -- reverse all the edges with respect to @v@: make @v@ a new root of the auxiliary tree.
  reverseNode lct v
  pushNode lct v

-- | Amortized \(O(\log N)\).
{-# INLINE write #-}
write :: (PrimMonad m, Monoid a, VU.Unbox a) => Lct (PrimState m) a -> Vertex -> a -> m ()
write lct v x = do
  -- make @v@ the new root of the underlying tree:
  evert lct v
  VGM.unsafeWrite (vLct lct) v x

-- | Amortized \(O(\log N)\).
{-# INLINE modify #-}
modify :: (PrimMonad m, Monoid a, VU.Unbox a) => Lct (PrimState m) a -> (a -> a) -> Vertex -> m ()
modify lct f v = do
  -- make @v@ the new root of the underlying tree:
  evert lct v
  VGM.unsafeModify (vLct lct) f v

-- | Amortized \(O(\log N)\). Creates an edge between @(c, p)@. In the represented tree, parent of
-- @c@ is @p@ after the operation.
{-# INLINE link #-}
link :: (PrimMonad m, Monoid a, VU.Unbox a) => Lct (PrimState m) a -> Vertex -> Vertex -> m ()
link lct@Lct {pLct, rLct} c p = do
  -- make @c@ the new root of the underlying tree
  evert lct c
  -- remove right children of @p@.
  expose_ lct p
  pushNode lct p

  -- connect with a heavy edge:
  VGM.unsafeWrite pLct c p
  VGM.unsafeWrite rLct p c
  updateNodeLct lct p

-- | Amortized \(O(\log N)\). Deletes an edge between @(u, v)@.
{-# INLINE cut #-}
cut :: (PrimMonad m, Monoid a, VU.Unbox a) => Lct (PrimState m) a -> IndexLct -> IndexLct -> m ()
cut lct@Lct {pLct, lLct} u v = do
  -- make @u@ the new root of the underlying tree
  evert lct u
  -- make @v@ in the same preferred path as the root
  expose_ lct v

  -- delete the heavy edge.
  vl <- VGM.unsafeRead lLct v
  VGM.unsafeWrite pLct vl undefLct
  VGM.unsafeWrite lLct v undefLct
  updateNodeLct lct v

-- | Amortized \(O(\log N)\). Folds a path between @(u, v)@.
{-# INLINE prodPath #-}
prodPath :: (PrimMonad m, Monoid a, VU.Unbox a) => Lct (PrimState m) a -> IndexLct -> IndexLct -> m a
prodPath lct@Lct {aggLct} u v = do
  -- make @u@ the root of the underlying tree
  evert lct u
  -- make @v@ in the same preferred path as @u@
  expose_ lct v
  -- now that @v@ is at the root of the auxiliary tree, its aggregation value is the path folding:
  VGM.unsafeRead aggLct v

# This file was generated by nvfetcher, please do not modify it manually.
{ fetchgit, fetchurl, fetchFromGitHub, dockerTools }:
{
  oj-verify = {
    pname = "oj-verify";
    version = "adbff121b1f96de5f34e9f1483eb47d661c54075";
    src = fetchFromGitHub {
      owner = "online-judge-tools";
      repo = "verification-helper";
      rev = "adbff121b1f96de5f34e9f1483eb47d661c54075";
      fetchSubmodules = false;
      sha256 = "sha256-f7Ge8kLRQv9uxdNGtgNsypGVY0XAnKPCg8HYQ5nT6mI=";
    };
    date = "2024-10-09";
  };
}

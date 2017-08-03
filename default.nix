{ pkgs ? (import <nixpkgs> { config = {
    allowUnfree = true;         # because we haven't set license params
    allowBroken = true;
  };})
}:

let
  haskellPkgs = pkgs.haskell.packages.ghc802;

  inherit (pkgs) stdenv;
  inherit (pkgs.haskell.lib) dontCheck dontHaddock;

  callPackage = stdenv.lib.callPackageWith (pkgs // haskellPkgs // haskellDeps);

  withSrc = path: deriv: pkgs.stdenv.lib.overrideDerivation deriv (attrs: {
    src = path;
  });

  withPatches = patches: deriv: pkgs.stdenv.lib.overrideDerivation deriv (attrs: {
    patches = patches;
  });

  haskellDeps = pkgs.recurseIntoAttrs rec {
  #   lngen = withSrc ./lngen (callPackage ./lngen.nix {});
  };

  dependencies = rec {
    QuickChick = withPatches [./QuickChick.patch]
      (callPackage ./QuickChick.nix {});

    # metalib = callPackage ./metalib.nix {
    #   haskellPackages = haskellPkgs // haskellDeps;
    # };
  };

  software = with pkgs; [
    # Why3
    why3

    # Coq
    ocaml
    ocamlPackages.camlp5_transitional
    coq_8_6
    coqPackages_8_6.dpdgraph
    coqPackages_8_6.coq-ext-lib

    # QuickChick
    dependencies.QuickChick

    # Ott
    ott

    # lngen
    # haskellDeps.lngen

    # Metalib
    # dependencies.metalib

    # Editors
    vim
    emacs
      emacsPackages.proofgeneral_HEAD
      emacsPackagesNg.use-package
      emacsPackagesNg.company-coq
      emacsPackagesNg.tuareg
      emacsPackagesNg.dash
  ];

  build = with pkgs; pkgs.buildEnv {
    name = "fcat";
    paths = software;
  };

in rec {
  env = with pkgs; pkgs.myEnvFun {
    name = "fcat";
    buildInputs = software;
  };

  options = {
    dependencies = dependencies;
    build = build;
  };
}

{ pkgs ? import dep/nixpkgs {}
}:

let
  haskellPackages = pkgs.haskellPackages.extend
    (import ./. { inherit (pkgs) lib; });
in {
  inherit haskellPackages;
  inherit (haskellPackages) groundhog groundhog-postgresql groundhog-th;
}

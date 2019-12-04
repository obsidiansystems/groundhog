{ pkgs ? import dep/nixpkgs {}
}:
let
  haskellPackages = pkgs.haskellPackages.extend (self: super:
    let
      packages = ns: pkgs.lib.genAttrs ns (name: self.callCabal2nix name (./. + "/${name}") {});
    in packages [
      "examples"
      "groundhog"
      "groundhog-inspector"
      "groundhog-mysql"
      "groundhog-postgresql"
      "groundhog-sqlite"
      "groundhog-test"
      "groundhog-th"
    ]);
in {
  inherit haskellPackages;
  inherit (haskellPackages) groundhog groundhog-postgresql groundhog-th;
}

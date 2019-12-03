{ lib }:

self: super:

let
  packages = ns: lib.genAttrs ns (name: self.callCabal2nix name (./. + "/${name}") {});
in packages [
  "examples"
  "groundhog"
  "groundhog-inspector"
  "groundhog-mysql"
  "groundhog-postgresql"
  "groundhog-sqlite"
  "groundhog-test"
  "groundhog-th"
]

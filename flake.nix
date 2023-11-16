{
  description = "FormalSystems lean implementation";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-23.05";
    flake-utils.url = "github:numtide/flake-utils";
    lean = {
      url = "github:leanprover/lean4/v4.2.0";
      inputs = {
        flake-utils.follows = "flake-utils";
        nixpkgs.follows = "nixpkgs";
      };
    };
  };

  outputs = inputs @ {
    self,
    flake-utils,
    nixpkgs,
    ...
  }:
    flake-utils.lib.eachSystem ["x86_64-linux"] (system: let
      pkgs = import nixpkgs {system = system;};
      leanPkgs = inputs.lean.packages.${system};

      overrides = {
        std.name = "Std";
        aesop.name = "Aesop";
        mathlib.name = "Mathlib";
        proofwidgets.name = "ProofWidgets";
      };

      inherit (pkgs) lib;
      inherit (leanPkgs) buildLeanPackage;
      inherit (lib) mapAttrs attrValues;

      dependenciesFromLakeManifest = path: let
        inherit (builtins) fromJSON readFile fetchGit pathExists;
        inherit (lib) listToAttrs nameValuePair optionalAttrs;

        manifest = fromJSON (readFile path);
        lakePackages =
          listToAttrs
          (map (pkg: nameValuePair pkg.git.name pkg.git) manifest.packages);

        fetchLakePackage = name:
          fetchGit {
            inherit name;
            inherit (lakePackages."${name}") url rev;
          };

        buildLakePackage = name: let
          src = fetchLakePackage name;

          inner-manifest = "${src}/lake-manifest.json";
          deps = optionalAttrs (pathExists inner-manifest) {
            deps =
              attrValues (dependenciesFromLakeManifest inner-manifest);
          };

          package = buildLeanPackage ({inherit name src;} // deps);
        in
          package.override (overrides."${name}" or {});
      in
        mapAttrs (name: _: buildLakePackage name) lakePackages;

      dependencies = dependenciesFromLakeManifest ./lake-manifest.json;
      lakePkgs = mapAttrs (_: value: value.modRoot) dependencies;

      package = buildLeanPackage {
        name = "FormalSystems";
        src = ./.;
        deps = attrValues dependencies;
      };
    in {
      packages =
        lakePkgs
        // rec {
          inherit (leanPkgs) lean lean-all;

          FormalSystems = package.modRoot;
          default = FormalSystems;
        };

      devShells.default = package.devShell;

      formatter = pkgs.alejandra;
    });
}
# Local Variables:
# apheleia-formatter: alejandra
# End:

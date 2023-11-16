{
  description = "FormalSystems lean implementation";

  inputs = {
    lean.url = "github:leanprover/lean4/v4.2.0";
    flake-utils.url = "github:numtide/flake-utils";
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-23.05";
  };

  outputs = { self, lean, flake-utils, nixpkgs }: flake-utils.lib.eachDefaultSystem (system:
    let
      leanPkgs = lean.packages.${system};
      pkgs = import nixpkgs { system = system; };
      leanDeps = map
        (dep: {
          path = builtins.fetchGit {
            inherit (dep.git) url rev name;
          };
          inherit (dep.git) name;
        })
        (builtins.fromJSON (builtins.readFile ./lake-manifest.json)).packages;
      pkg = pkgs.stdenv.mkDerivation {
        name = "formal-systems";
        src = ./.;
        nativeBuildInputs = [ leanPkgs pkgs.git ];
        buildPhase = ''
          ln -sf ${leanPkgs.lean-all}/* .
          mkdir -p ./lake-packages
          ${builtins.concatStringsSep "&&" (map (dep: "cp -r " + dep.path + " ./lake-packages/" + dep.name) leanDeps)}
          bin/lake --version
          bin/lake build
        '';
      };
    in
    {
      packages = {
        default = pkg;
        inherit (leanPkgs) lean;
      };
    });
}

{
  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs";
    flake-parts = {
      url = "github:numtide/flake-utils";
      inputs.nixpkgs.follows = "nixpkgs";
    };
  };
  outputs = { nixpkgs, flake-utils, ... }: flake-utils.lib.eachDefaultSystem (system:
    let
      pkgs = nixpkgs.legacyPackages.${system};
      ghcVer = "912";
    in {
      devShells.default = pkgs.mkShell {
        buildInputs = with pkgs; [
          cabal-install
          haskell.compiler."ghc${ghcVer}"
          (haskell-language-server.override { supportedGhcVersions = [ ghcVer ];})
        ];
      };
    }
  );
}

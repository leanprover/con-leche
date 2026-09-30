# whitepaper/flake.nix — the document toolchain (task #324).
#
# `nix develop ./whitepaper -c whitepaper/build.sh` from the repo root,
# or `direnv allow` inside this directory and then `./build.sh`.
# The lock file pins nixpkgs; `typst --version` must stay >= 0.15
# (HTML export with native MathML, `html.elem`, `target()`).
{
  description = "ConLeche whitepaper: Typst toolchain";

  inputs.nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";

  outputs = { self, nixpkgs }:
    let
      systems = [ "x86_64-linux" "aarch64-linux" "x86_64-darwin" "aarch64-darwin" ];
      forAll = f: nixpkgs.lib.genAttrs systems (system: f nixpkgs.legacyPackages.${system});
    in {
      devShells = forAll (pkgs: {
        default = pkgs.mkShell {
          packages = [
            pkgs.typst        # the ONE source of truth renders to PDF and HTML
            pkgs.libertinus   # Libertinus Sans for headings (Serif is embedded in typst)
            pkgs.python3      # links-gate.sh, build.sh's warning filter
          ];
          # typst finds the sans face here; build.sh passes --ignore-system-fonts,
          # so the PDF is the same on every machine.
          TYPST_FONT_PATHS = "${pkgs.libertinus}/share/fonts";
          # Never contact the package registry: lib.typ uses no packages.
          TYPST_PACKAGE_PATH = "/var/empty";
        };
      });
    };
}

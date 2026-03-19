#!/usr/bin/env python3

from __future__ import annotations

import argparse
import html
import os
import re
from dataclasses import dataclass, field
from pathlib import Path


NAVBAR_NAME = "navbar-demazure.html"
IMPORT_RE = re.compile(r"^\s*import\s+([A-Za-z0-9_.]+)\s*$")
IFRAME_RE = re.compile(
    r'(<iframe src=")([^"]*navbar(?:-demazure)?\.html)(" class="navframe")'
)


@dataclass
class ModuleNode:
    name: str
    module: str | None = None
    children: dict[str, "ModuleNode"] = field(default_factory=dict)


def parse_args() -> argparse.Namespace:
    script_path = Path(__file__).resolve()
    repo_root = script_path.parents[1]
    default_docs_root = repo_root / "docbuild" / ".lake" / "build" / "doc"
    parser = argparse.ArgumentParser(
        description=(
            "Generate a Demazure-only navbar for doc-gen4 output and rewrite "
            "Demazure pages to use it."
        )
    )
    parser.add_argument(
        "--repo-root",
        type=Path,
        default=repo_root,
        help="Path to the repository root containing Demazure.lean.",
    )
    parser.add_argument(
        "--docs-root",
        type=Path,
        default=default_docs_root,
        help="Path to the generated doc-gen4 output directory.",
    )
    return parser.parse_args()


def read_root_imports(repo_root: Path) -> list[str]:
    root_file = repo_root / "Demazure.lean"
    imports: list[str] = []
    for line in root_file.read_text(encoding="utf-8").splitlines():
        match = IMPORT_RE.match(line)
        if match is None:
            continue
        module = match.group(1)
        if module.startswith("Demazure."):
            imports.append(module)
    return imports


def discover_modules(repo_root: Path) -> list[str]:
    modules: list[str] = []
    for lean_file in sorted((repo_root / "Demazure").rglob("*.lean")):
        rel = lean_file.relative_to(repo_root).with_suffix("")
        modules.append(".".join(rel.parts))
    return modules


def ordered_modules(repo_root: Path) -> list[str]:
    modules = ["Demazure"]
    seen = {"Demazure"}
    for module in read_root_imports(repo_root):
        if module not in seen:
            modules.append(module)
            seen.add(module)
    for module in discover_modules(repo_root):
        if module not in seen:
            modules.append(module)
            seen.add(module)
    return modules


def module_to_doc_path(module: str) -> Path:
    if module == "Demazure":
        return Path("Demazure.html")
    return Path(*module.split(".")).with_suffix(".html")


def build_tree(modules: list[str]) -> ModuleNode:
    root = ModuleNode(name="Demazure", module="Demazure")
    for module in modules:
        if module == "Demazure":
            continue
        parts = module.split(".")
        if not parts or parts[0] != "Demazure":
            continue
        node = root
        for part in parts[1:]:
            node = node.children.setdefault(part, ModuleNode(name=part))
        node.module = module
    return root


def render_nav_entry(node: ModuleNode) -> str:
    label = html.escape(node.name)
    if node.module is None:
        href = None
    else:
        href = f"./{module_to_doc_path(node.module).as_posix()}"
    if not node.children:
        if href is None:
            raise ValueError(f"Leaf node {node.name} has no module path")
        return f'<div class="nav_link"><a href="{href}">{label}</a></div>'

    child_html = "\n".join(render_nav_entry(child) for child in node.children.values())
    attrs = ['class="nav_sect"']
    if href is not None:
        attrs.append(f'data-path="{href}"')
        summary = f'{label} (<a href="{href}">file</a>)'
    else:
        summary = label
    attrs_text = " ".join(attrs)
    return (
        f"<details {attrs_text}><summary>{summary}</summary>\n"
        f"{child_html}\n"
        f"</details>"
    )


def navbar_html(module_tree: ModuleNode) -> str:
    module_list = render_nav_entry(module_tree)
    return f"""<html lang="en"><head><meta charset="UTF-8"></meta><meta name="viewport" content="width=device-width, initial-scale=1"></meta><link rel="stylesheet" href="./style.css"></link><link rel="icon" href="./favicon.svg"></link><link rel="mask-icon" href="./favicon.svg" color="#000000"></link><link rel="prefetch" href=".//declarations/declaration-data.bmp" as="image"></link><script type="module" src="./nav.js"></script><script type="module" src="./color-scheme.js"></script><base target="_parent"></base></head><body><div class="navframe"><nav class="nav"><h3>General documentation</h3><div class="nav_link"><a href="./">index</a></div><div class="nav_link"><a href="./foundational_types.html">foundational types</a></div><h3>Library</h3><div class="module_list">{module_list}</div><div id="settings" hidden="hidden"><h3>Color scheme</h3><form id="color-theme-switcher"><label for="color-theme-dark"><input type="radio" name="color_theme" id="color-theme-dark" value="dark" autocomplete="off"></input>dark</label><label for="color-theme-system" title="Match system theme settings"><input type="radio" name="color_theme" id="color-theme-system" value="system" autocomplete="off"></input>system</label><label for="color-theme-light"><input type="radio" name="color_theme" id="color-theme-light" value="light" autocomplete="off"></input>light</label></form></div></nav></div></body></html>
"""


def rewrite_navbar_iframe(page: Path, docs_root: Path) -> bool:
    text = page.read_text(encoding="utf-8")
    relative_navbar = os.path.relpath(docs_root / NAVBAR_NAME, page.parent)
    relative_navbar = relative_navbar.replace(os.sep, "/")

    def repl(match: re.Match[str]) -> str:
        return f'{match.group(1)}{relative_navbar}{match.group(3)}'

    new_text, count = IFRAME_RE.subn(repl, text, count=1)
    if count == 0:
        return False
    if new_text != text:
        page.write_text(new_text, encoding="utf-8")
    return True


def main() -> int:
    args = parse_args()
    repo_root = args.repo_root.resolve()
    docs_root = args.docs_root.resolve()

    if not (repo_root / "Demazure.lean").exists():
        raise FileNotFoundError(f"Could not find Demazure.lean under {repo_root}")
    if not docs_root.exists():
        raise FileNotFoundError(f"Could not find docs directory {docs_root}")

    modules = ordered_modules(repo_root)
    module_tree = build_tree(modules)

    navbar_path = docs_root / NAVBAR_NAME
    navbar_path.write_text(navbar_html(module_tree), encoding="utf-8")

    rewritten: list[Path] = []
    missing: list[Path] = []
    unchanged: list[Path] = []

    for module in modules:
        page = docs_root / module_to_doc_path(module)
        if not page.exists():
            missing.append(page)
            continue
        if rewrite_navbar_iframe(page, docs_root):
            rewritten.append(page)
        else:
            unchanged.append(page)

    print(f"Wrote {navbar_path}")
    print(f"Rewrote {len(rewritten)} Demazure doc page(s)")
    for page in rewritten:
        print(f"  {page.relative_to(docs_root)}")
    if missing:
        print("Missing expected doc page(s):")
        for page in missing:
            print(f"  {page.relative_to(docs_root)}")
    if unchanged:
        print("Could not find a navbar iframe in:")
        for page in unchanged:
            print(f"  {page.relative_to(docs_root)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

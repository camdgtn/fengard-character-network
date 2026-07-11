#!/usr/bin/env python3
from __future__ import annotations

import argparse
import csv
import hashlib
import html
import mimetypes
import os
import re
import shutil
import subprocess
import tempfile
import zipfile
from collections import Counter
from pathlib import Path
from urllib.parse import unquote, urlparse

from bs4 import BeautifulSoup
from lxml import etree

W_NS = 'http://schemas.openxmlformats.org/wordprocessingml/2006/main'
R_NS = 'http://schemas.openxmlformats.org/officeDocument/2006/relationships'
A_NS = 'http://schemas.openxmlformats.org/drawingml/2006/main'
V_NS = 'urn:schemas-microsoft-com:vml'
WP_NS = 'http://schemas.openxmlformats.org/drawingml/2006/wordprocessingDrawing'
PKG_REL_NS = 'http://schemas.openxmlformats.org/package/2006/relationships'
NS = {'w': W_NS, 'r': R_NS, 'a': A_NS, 'v': V_NS, 'wp': WP_NS, 'pr': PKG_REL_NS}
W = '{' + W_NS + '}'
R = '{' + R_NS + '}'

DARK_RED = {'800000', '8B0000', '990000', '9C0006', 'A00000', 'B00000', 'C00000', 'CC0000'}
BLUE = {'0000FF', '0000CC', '0033CC', '1F4E79', '0563C1'}
WHITE = {'FFFFFF', 'FFF', 'F2F2F2'}

BASE_CSS = r'''
:root {
  --parchment: #d1b64f;
  --parchment-light: #eadb97;
  --parchment-pale: #f3e8b9;
  --ink: #191207;
  --wine: #7f0e0e;
  --wine-dark: #560707;
  --blue: #063bcc;
  --rule: rgba(74, 48, 13, .34);
}
* { box-sizing: border-box; }
html { min-height: 100%; background: #d8c16b; }
body {
  margin: 0;
  min-height: 100%;
  color: var(--ink);
  font-family: Georgia, 'Times New Roman', serif;
  background:
    radial-gradient(circle at 16% 8%, rgba(255,255,255,.38), transparent 31rem),
    linear-gradient(90deg, rgba(90,55,12,.10), transparent 10%, transparent 90%, rgba(90,55,12,.10)),
    #d8c16b;
}
a { color: #5b130c; }
.archive-bar {
  position: sticky; top: 0; z-index: 20;
  display: flex; align-items: center; justify-content: space-between; gap: 1rem;
  padding: .55rem clamp(.8rem, 3vw, 1.6rem);
  color: #f8edc2;
  background: linear-gradient(#6e1710, #4c0907);
  border-bottom: 3px ridge #c3a758;
  box-shadow: 0 2px 10px rgba(0,0,0,.3);
  font: 700 .82rem/1.2 Arial, sans-serif;
}
.archive-bar a { color: #fff5cb; text-decoration: none; }
.archive-bar a:hover { text-decoration: underline; }
.page-wrap { width: min(1180px, calc(100% - 24px)); margin: 18px auto 50px; }
.source-card {
  border: 3px ridge #8e6924;
  background: linear-gradient(rgba(255,255,255,.05), rgba(255,255,255,.01)), var(--parchment);
  box-shadow: 0 12px 35px rgba(57,31,0,.25), inset 0 0 42px rgba(255,247,191,.25);
}
.source-header {
  padding: 1rem 1.25rem .85rem;
  border-bottom: 3px double rgba(82,48,4,.56);
  background: linear-gradient(180deg, rgba(250,231,154,.85), rgba(208,182,79,.82));
}
.source-header h1 { margin: 0; font-size: clamp(1.45rem, 4vw, 2.25rem); line-height: 1.05; }
.source-meta { margin-top: .5rem; color: #553c16; font: .78rem/1.45 Arial, sans-serif; }
.source-body { padding: clamp(.65rem, 2.5vw, 1.45rem); overflow-wrap: anywhere; }
.doc-line, .legacy-content p, .fallback-content article {
  margin: 0 0 .42rem;
  line-height: 1.28;
}
.doc-line.turn-line { margin-bottom: .48rem; }
.doc-line.spacer { min-height: .55rem; margin: 0; }
.doc-line.fate-line {
  display: block;
  width: fit-content;
  max-width: 100%;
  margin: 1.2rem auto;
  padding: .25rem .52rem .32rem;
  color: #fff !important;
  background: var(--wine);
  border: 1px solid #f0d386;
  box-shadow: 0 0 0 2px var(--wine), 0 3px 9px rgba(55,0,0,.18);
  font-family: Arial, Helvetica, sans-serif;
  font-weight: 800;
  text-align: center;
  line-height: 1.08;
}
.doc-line.dice-line { color: var(--blue); font-weight: 600; }
.dice-run { color: var(--blue) !important; }
.action-run { color: #980e08 !important; }
.inline-icon {
  display: inline-block;
  width: auto;
  max-width: 42px;
  max-height: 30px;
  margin: 0 .18rem;
  vertical-align: -.35em;
  image-rendering: auto;
}
.doc-line img.inline-icon[src$='.gif'] { image-rendering: auto; }
.legacy-content { max-width: 100%; }
.legacy-content img { max-width: 100%; height: auto; }
.legacy-content, .legacy-content > * { max-width: 100% !important; }
.legacy-content table { width: auto !important; max-width: 100% !important; }
.missing-icon { display:inline-block; min-width:1.1em; color:#5b130c; font-weight:700; text-align:center; vertical-align:baseline; }
.legacy-content table { max-width: 100%; border-collapse: collapse; }
.legacy-content td, .legacy-content th { padding: .2rem; }
.fallback-content article { padding: .4rem 0 .65rem; border-bottom: 1px solid var(--rule); }
.fallback-content h2 { margin: 0 0 .2rem; font: 700 1rem/1.3 Arial, sans-serif; }
.fallback-content .time { font-weight: 400; color: #5a421c; }
.render-note {
  margin: 1.1rem 0 0;
  padding: .6rem .75rem;
  color: #5a421c;
  border-top: 1px solid var(--rule);
  font: .72rem/1.4 Arial, sans-serif;
}
@media (max-width: 680px) {
  .archive-bar { position: static; align-items: flex-start; flex-direction: column; gap: .3rem; }
  .page-wrap { width: min(100% - 10px, 1180px); margin-top: 5px; }
  .source-card { border-width: 2px; }
  .source-header { padding: .75rem .8rem; }
  .source-body { padding: .62rem; font-size: .98rem; }
  .doc-line.fate-line { width: 100%; font-size: .96rem; }
  .inline-icon { max-height: 25px; max-width: 34px; }
}
'''


def slug_id(value: str) -> str:
    return hashlib.sha1(value.encode('utf-8', errors='replace')).hexdigest()[:12]


def safe_filename(name: str) -> str:
    cleaned = re.sub(r'[^A-Za-z0-9._-]+', '_', name).strip('._')
    return cleaned or 'asset'


def read_csv(path: Path) -> list[dict[str, str]]:
    with path.open('r', encoding='utf-8-sig', errors='replace', newline='') as fh:
        return list(csv.DictReader(fh))


def qn(tag: str) -> str:
    prefix, local = tag.split(':')
    return '{' + NS[prefix] + '}' + local


def value_attr(node, attr='val') -> str:
    if node is None:
        return ''
    return node.get(W + attr, '') or ''


def bool_prop(node) -> bool:
    if node is None:
        return False
    value = node.get(W + 'val')
    return value not in {'0', 'false', 'False', 'off'}


def clean_hex(value: str) -> str:
    value = (value or '').strip().lstrip('#').upper()
    if value in {'AUTO', 'NONE', 'NIL'}:
        return ''
    if re.fullmatch(r'[0-9A-F]{3}|[0-9A-F]{6}', value):
        if len(value) == 3:
            value = ''.join(c * 2 for c in value)
        return value
    return ''


def color_is_dark_red(value: str) -> bool:
    value = clean_hex(value)
    if value in DARK_RED:
        return True
    if len(value) != 6:
        return False
    r, g, b = int(value[:2], 16), int(value[2:4], 16), int(value[4:], 16)
    return r >= 75 and r > g * 1.8 and r > b * 1.8 and g < 75 and b < 75


def color_is_blue(value: str) -> bool:
    value = clean_hex(value)
    if value in BLUE:
        return True
    if len(value) != 6:
        return False
    r, g, b = int(value[:2], 16), int(value[2:4], 16), int(value[4:], 16)
    return b >= 120 and b > r * 1.6 and b > g * 1.15


def color_is_white(value: str) -> bool:
    value = clean_hex(value)
    if value in WHITE:
        return True
    if len(value) != 6:
        return False
    return all(int(value[i:i+2], 16) > 225 for i in (0, 2, 4))


def parse_docx_relationships(zf: zipfile.ZipFile) -> dict[str, str]:
    rel_path = 'word/_rels/document.xml.rels'
    if rel_path not in zf.namelist():
        return {}
    root = etree.fromstring(zf.read(rel_path))
    out = {}
    for rel in root:
        rid = rel.get('Id')
        target = rel.get('Target')
        if rid and target:
            if target.startswith('/'):
                package_path = target.lstrip('/')
            else:
                package_path = str(Path('word') / target)
            out[rid] = str(Path(package_path))
    return out


def parse_style_map(zf: zipfile.ZipFile) -> tuple[dict[str, dict], dict[str, dict], dict]:
    paragraph_styles: dict[str, dict] = {}
    run_styles: dict[str, dict] = {}
    defaults: dict = {}
    if 'word/styles.xml' not in zf.namelist():
        return paragraph_styles, run_styles, defaults
    root = etree.fromstring(zf.read('word/styles.xml'))
    doc_defaults = root.find('w:docDefaults', NS)
    if doc_defaults is not None:
        rpr = doc_defaults.find('.//w:rPrDefault/w:rPr', NS)
        if rpr is not None:
            defaults = extract_run_props(rpr)
    for style in root.findall('w:style', NS):
        style_id = style.get(W + 'styleId', '')
        style_type = style.get(W + 'type', '')
        based = style.find('w:basedOn', NS)
        props = {
            'based_on': value_attr(based),
            'run': extract_run_props(style.find('w:rPr', NS)),
            'paragraph': extract_paragraph_props(style.find('w:pPr', NS)),
        }
        if style_type == 'paragraph':
            paragraph_styles[style_id] = props
        elif style_type == 'character':
            run_styles[style_id] = props
    return paragraph_styles, run_styles, defaults


def merge_props(*items: dict) -> dict:
    out: dict = {}
    for item in items:
        if item:
            out.update({k: v for k, v in item.items() if v not in ('', None)})
    return out


def resolve_style(style_id: str, styles: dict[str, dict], key: str, seen=None) -> dict:
    if not style_id or style_id not in styles:
        return {}
    seen = seen or set()
    if style_id in seen:
        return {}
    seen.add(style_id)
    style = styles[style_id]
    return merge_props(resolve_style(style.get('based_on', ''), styles, key, seen), style.get(key, {}))


def extract_run_props(rpr) -> dict:
    if rpr is None:
        return {}
    fonts = rpr.find('w:rFonts', NS)
    color = rpr.find('w:color', NS)
    shd = rpr.find('w:shd', NS)
    highlight = rpr.find('w:highlight', NS)
    sz = rpr.find('w:sz', NS)
    vert = rpr.find('w:vertAlign', NS)
    return {
        'bold': bool_prop(rpr.find('w:b', NS)),
        'italic': bool_prop(rpr.find('w:i', NS)),
        'underline': bool_prop(rpr.find('w:u', NS)),
        'strike': bool_prop(rpr.find('w:strike', NS)),
        'color': clean_hex(value_attr(color)),
        'background': clean_hex(value_attr(shd, 'fill')),
        'highlight': value_attr(highlight),
        'size_half_points': value_attr(sz),
        'font': (fonts.get(W + 'ascii', '') if fonts is not None else ''),
        'vert_align': value_attr(vert),
        'hidden': bool_prop(rpr.find('w:vanish', NS)),
    }


def extract_paragraph_props(ppr) -> dict:
    if ppr is None:
        return {}
    shd = ppr.find('w:shd', NS)
    jc = ppr.find('w:jc', NS)
    ind = ppr.find('w:ind', NS)
    spacing = ppr.find('w:spacing', NS)
    return {
        'background': clean_hex(value_attr(shd, 'fill')),
        'align': value_attr(jc),
        'left_twips': (ind.get(W + 'left', '') if ind is not None else ''),
        'right_twips': (ind.get(W + 'right', '') if ind is not None else ''),
        'first_line_twips': (ind.get(W + 'firstLine', '') if ind is not None else ''),
        'space_before_twips': (spacing.get(W + 'before', '') if spacing is not None else ''),
        'space_after_twips': (spacing.get(W + 'after', '') if spacing is not None else ''),
    }


def css_from_run_props(props: dict) -> tuple[str, list[str]]:
    css = []
    classes = []
    if props.get('bold'):
        css.append('font-weight:700')
    if props.get('italic'):
        css.append('font-style:italic')
    decorations = []
    if props.get('underline'):
        decorations.append('underline')
    if props.get('strike'):
        decorations.append('line-through')
    if decorations:
        css.append('text-decoration:' + ' '.join(decorations))
    color = props.get('color', '')
    bg = props.get('background', '')
    if color:
        css.append(f'color:#{color}')
        if color_is_blue(color):
            classes.append('dice-run')
        if color_is_dark_red(color):
            classes.append('action-run')
    if bg:
        css.append(f'background-color:#{bg}')
    if props.get('size_half_points'):
        try:
            css.append(f"font-size:{float(props['size_half_points'])/2:.2f}pt")
        except ValueError:
            pass
    if props.get('font'):
        css.append('font-family:' + html.escape(props['font']) + ', serif')
    if props.get('vert_align') == 'superscript':
        css.append('vertical-align:super;font-size:.75em')
    elif props.get('vert_align') == 'subscript':
        css.append('vertical-align:sub;font-size:.75em')
    if props.get('hidden'):
        css.append('display:none')
    return ';'.join(css), classes


def paragraph_css(props: dict) -> str:
    css = []
    if props.get('background'):
        css.append(f"background-color:#{props['background']}")
    align = props.get('align')
    if align in {'center', 'right', 'left', 'both', 'justify'}:
        css.append('text-align:' + ('justify' if align in {'both', 'justify'} else align))
    for key, css_name in [('left_twips', 'padding-left'), ('right_twips', 'padding-right')]:
        if props.get(key):
            try:
                css.append(f"{css_name}:{int(props[key])/20:.2f}pt")
            except ValueError:
                pass
    for key, css_name in [('space_before_twips', 'margin-top'), ('space_after_twips', 'margin-bottom')]:
        if props.get(key):
            try:
                css.append(f"{css_name}:{int(props[key])/20:.2f}pt")
            except ValueError:
                pass
    return ';'.join(css)


def extract_docx_image(zf, rels, rid: str, asset_dir: Path, used_names: Counter, image_cache: dict[str, str]) -> tuple[str, str] | None:
    package_path = rels.get(rid)
    if not package_path or package_path not in zf.namelist():
        return None
    if package_path in image_cache:
        name = image_cache[package_path]
        return name, mimetypes.guess_type(name)[0] or ''
    original = Path(package_path).name
    stem, suffix = Path(original).stem, Path(original).suffix
    used_names[original] += 1
    name = safe_filename(original)
    if used_names[original] > 1:
        name = safe_filename(f'{stem}_{used_names[original]}{suffix}')
    target = asset_dir / name
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_bytes(zf.read(package_path))
    image_cache[package_path] = name
    return name, mimetypes.guess_type(name)[0] or ''


def render_run(run, zf, rels, asset_dir, asset_rel_prefix, used_names, image_cache, style_props) -> tuple[str, dict]:
    rpr = run.find('w:rPr', NS)
    direct = extract_run_props(rpr)
    rstyle = value_attr(rpr.find('w:rStyle', NS)) if rpr is not None else ''
    resolved = merge_props(style_props.get('defaults', {}), resolve_style(rstyle, style_props.get('run_styles', {}), 'run'), direct)
    css, classes = css_from_run_props(resolved)
    pieces = []
    plain_pieces = []
    has_image = False
    for node in run.iterchildren():
        if node.tag == W + 'rPr':
            continue
        if node.tag == W + 't':
            pieces.append(html.escape(node.text or ''))
            plain_pieces.append(node.text or '')
        elif node.tag == W + 'tab':
            pieces.append('<span class="doc-tab">&emsp;</span>')
            plain_pieces.append('\t')
        elif node.tag in {W + 'br', W + 'cr'}:
            pieces.append('__LINE_BREAK__')
        elif node.tag == W + 'noBreakHyphen':
            pieces.append('&#8209;')
        elif node.tag == W + 'softHyphen':
            pieces.append('&shy;')
        elif node.tag in {W + 'drawing', W + 'pict', W + 'object'}:
            rids = node.xpath('.//@r:embed | .//@r:id', namespaces=NS)
            for rid in rids:
                result = extract_docx_image(zf, rels, rid, asset_dir, used_names, image_cache)
                if result:
                    filename, _mime = result
                    pieces.append(f'<img class="inline-icon" src="{html.escape(asset_rel_prefix + filename)}" alt="">')
                    has_image = True
    content = ''.join(pieces)
    if not content:
        return '', {'props': resolved, 'has_image': has_image, 'text_plain': ''.join(plain_pieces)}
    class_attr = ' '.join(classes)
    attrs = []
    if class_attr:
        attrs.append(f'class="{class_attr}"')
    if css:
        attrs.append(f'style="{css}"')
    return f"<span {' '.join(attrs)}>{content}</span>" if attrs else content, {'props': resolved, 'has_image': has_image, 'text_plain': ''.join(plain_pieces)}


def split_rendered_run(html_fragment: str) -> list[str]:
    if '__LINE_BREAK__' not in html_fragment:
        return [html_fragment]
    # A line break inside a styled span must close and reopen that span. Use a tiny soup parser.
    if not html_fragment.startswith('<span'):
        return html_fragment.split('__LINE_BREAK__')
    m = re.match(r'(<span[^>]*>)(.*)</span>$', html_fragment, flags=re.S)
    if not m:
        return html_fragment.split('__LINE_BREAK__')
    opener, inner = m.groups()
    return [opener + part + '</span>' if part else '' for part in inner.split('__LINE_BREAK__')]


def render_docx(source: Path, output_html: Path, asset_dir: Path, title: str, date: str, source_file: str) -> dict:
    asset_dir.mkdir(parents=True, exist_ok=True)
    with zipfile.ZipFile(source) as zf:
        root = etree.fromstring(zf.read('word/document.xml'))
        rels = parse_docx_relationships(zf)
        pstyles, rstyles, defaults = parse_style_map(zf)
        style_props = {'paragraph_styles': pstyles, 'run_styles': rstyles, 'defaults': defaults}
        used_names = Counter()
        image_cache: dict[str, str] = {}
        rendered_lines = []
        line_index = 0
        for paragraph in root.xpath('.//w:body/w:p', namespaces=NS):
            ppr = paragraph.find('w:pPr', NS)
            pstyle_id = value_attr(ppr.find('w:pStyle', NS)) if ppr is not None else ''
            p_props = merge_props(resolve_style(pstyle_id, pstyles, 'paragraph'), extract_paragraph_props(ppr))
            current_parts: list[tuple[str, dict]] = []
            paragraph_lines: list[list[tuple[str, dict]]] = []
            children = list(paragraph)
            for child in children:
                runs = []
                if child.tag == W + 'r':
                    runs = [child]
                elif child.tag == W + 'hyperlink':
                    runs = child.findall('.//w:r', NS)
                elif child.tag in {W + 'bookmarkStart', W + 'bookmarkEnd', W + 'proofErr', W + 'permStart', W + 'permEnd'}:
                    continue
                for run in runs:
                    fragment, meta = render_run(run, zf, rels, asset_dir, '../assets/' + asset_dir.name + '/', used_names, image_cache, style_props)
                    fragments = split_rendered_run(fragment)
                    for idx, piece in enumerate(fragments):
                        if idx > 0:
                            paragraph_lines.append(current_parts)
                            current_parts = []
                        if piece:
                            current_parts.append((piece, meta))
            paragraph_lines.append(current_parts)
            for line in paragraph_lines:
                visible_html = ''.join(part for part, _ in line)
                plain = BeautifulSoup(visible_html, 'html.parser').get_text('', strip=False).replace('\xa0', ' ')
                plain_norm = re.sub(r'\s+', ' ', plain).strip()
                if not plain_norm and '<img' not in visible_html:
                    rendered_lines.append('<div class="doc-line spacer" aria-hidden="true"></div>')
                    continue
                run_props = [meta.get('props', {}) for _, meta in line]
                colors = [p.get('color', '') for p in run_props if p.get('color')]
                textual_blue = any(
                    color_is_blue(meta.get('props', {}).get('color', '')) and meta.get('text_plain', '').strip()
                    for _, meta in line
                )
                backgrounds = [p.get('background', '') for p in run_props if p.get('background')]
                p_bg = p_props.get('background', '')
                fate = (
                    color_is_dark_red(p_bg)
                    or any(color_is_dark_red(c) for c in backgrounds)
                    and any(color_is_white(c) for c in colors)
                )
                dice = textual_blue or bool(re.search(r'\btirando\s+i\s+dadi\b', plain_norm, re.I))
                classes = ['doc-line']
                if re.match(r'^\s*\d{1,2}:\d{2}', plain_norm):
                    classes.append('turn-line')
                if fate:
                    classes.append('fate-line')
                elif dice:
                    classes.append('dice-line')
                p_css = paragraph_css(p_props)
                # Avoid keeping original run background on fate lines: the container provides it cleanly.
                if fate:
                    visible_html = re.sub(r';?background-color:#[0-9A-Fa-f]{6}', '', visible_html)
                    visible_html = re.sub(r';?color:#[0-9A-Fa-f]{6}', '', visible_html)
                attrs = f'class="{" ".join(classes)}"'
                if p_css and not fate:
                    attrs += f' style="{p_css}"'
                rendered_lines.append(f'<div {attrs}>{visible_html}</div>')
                line_index += 1

    body = '\n'.join(rendered_lines)
    write_page(output_html, title, date, source_file, body, 'docx-rich', note='Formattazione, colori e immagini recuperati dal DOCX originale.')
    return {'status': 'rich_docx', 'lines': line_index, 'assets': len(image_cache)}


def rewrite_local_assets(soup: BeautifulSoup, source: Path, asset_dir: Path, asset_url_prefix: str) -> int:
    copied = 0
    seen = {}
    for tag in soup.find_all(src=True):
        raw = tag.get('src', '').strip()
        if not raw or raw.startswith(('data:', 'http://', 'https://', '//', '#')):
            continue
        parsed = unquote(urlparse(raw).path)
        candidate = (source.parent / parsed).resolve()
        if not candidate.exists() or not candidate.is_file():
            base = Path(parsed).name.lower()
            if base in {'m.gif', 'male.gif', 'maschio.gif'}:
                replacement = soup.new_tag('span', attrs={'class': 'missing-icon', 'title': 'Icona maschile storica'})
                replacement.string = '♂'
            elif base in {'f.gif', 'female.gif', 'femmina.gif'}:
                replacement = soup.new_tag('span', attrs={'class': 'missing-icon', 'title': 'Icona femminile storica'})
                replacement.string = '♀'
            else:
                replacement = soup.new_tag('span', attrs={'class': 'missing-icon', 'title': 'Icona storica non disponibile: ' + raw})
                replacement.string = '✦'
            tag.replace_with(replacement)
            continue
        key = str(candidate)
        if key in seen:
            tag['src'] = seen[key]
            continue
        name = safe_filename(candidate.name)
        target = asset_dir / name
        index = 2
        while target.exists() and target.read_bytes() != candidate.read_bytes():
            name = safe_filename(f'{candidate.stem}_{index}{candidate.suffix}')
            target = asset_dir / name
            index += 1
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(candidate, target)
        new_url = asset_url_prefix + name
        tag['src'] = new_url
        seen[key] = new_url
        copied += 1
    return copied


def clean_legacy_html(source: Path, asset_dir: Path, asset_url_prefix: str) -> tuple[str, int, str]:
    raw = source.read_text(encoding='utf-8', errors='replace')
    soup = BeautifulSoup(raw, 'html.parser')
    for tag in soup.find_all(['script', 'noscript', 'iframe', 'object', 'embed', 'form']):
        tag.decompose()
    for tag in soup.find_all('meta'):
        if tag.get('http-equiv', '').lower() in {'refresh', 'content-security-policy'}:
            tag.decompose()
    copied = rewrite_local_assets(soup, source, asset_dir, asset_url_prefix)
    # Inline local stylesheets where possible, remove irrelevant navigation links.
    styles = []
    for style in soup.find_all('style'):
        styles.append(style.get_text('\n'))
    for link in soup.find_all('link', href=True):
        if 'stylesheet' not in [x.lower() for x in (link.get('rel') or [])]:
            continue
        href = unquote(urlparse(link['href']).path)
        candidate = (source.parent / href).resolve()
        if candidate.exists() and candidate.is_file():
            styles.append(candidate.read_text(encoding='utf-8', errors='replace'))
        link.decompose()
    body = soup.body or soup
    # Strip ids/classes commonly used for fixed navigation, while preserving inline formatting.
    for tag in body.find_all(True):
        if tag.name in {'html', 'head', 'body'}:
            continue
        # Remove event handlers and potentially unsafe external links.
        for attr in list(tag.attrs):
            if attr.lower().startswith('on'):
                del tag.attrs[attr]
        if tag.name == 'a' and tag.get('href', '').lower().startswith(('javascript:', 'mailto:')):
            tag.attrs.pop('href', None)
    content = ''.join(str(x) for x in body.contents)
    style_blob = '\n'.join(styles)
    return f'<style class="legacy-original-styles">{style_blob}</style><div class="legacy-content">{content}</div>', copied, 'html-preserved'


def convert_doc_to_html(source: Path, temp_root: Path) -> Path | None:
    token = slug_id(str(source.resolve()))
    out_dir = temp_root / token / 'out'
    profile = temp_root / token / 'profile'
    out_dir.mkdir(parents=True, exist_ok=True)
    profile.mkdir(parents=True, exist_ok=True)
    command = [
        shutil.which('soffice') or shutil.which('libreoffice') or 'soffice',
        f'-env:UserInstallation={profile.resolve().as_uri()}',
        '--headless', '--nologo', '--nodefault', '--nolockcheck', '--nofirststartwizard',
        '--convert-to', 'html', '--outdir', str(out_dir), str(source),
    ]
    try:
        result = subprocess.run(command, capture_output=True, timeout=90)
    except subprocess.TimeoutExpired:
        return None
    candidates = list(out_dir.glob('*.html')) + list(out_dir.glob('*.htm'))
    return candidates[0] if result.returncode == 0 and candidates else None


def render_legacy(source: Path, output_html: Path, asset_dir: Path, title: str, date: str, source_file: str, temp_root: Path) -> dict:
    asset_dir.mkdir(parents=True, exist_ok=True)
    render_source = source
    mode = 'html-original'
    if source.suffix.lower() == '.doc':
        converted = convert_doc_to_html(source, temp_root)
        if converted is None:
            return {'status': 'fallback_required', 'lines': 0, 'assets': 0}
        render_source = converted
        mode = 'doc-via-libreoffice'
    body, copied, _ = clean_legacy_html(render_source, asset_dir, '../assets/' + asset_dir.name + '/')
    note = 'HTML originale ripulito e reso responsive.' if mode == 'html-original' else 'Formattazione recuperata dal vecchio Word tramite LibreOffice.'
    write_page(output_html, title, date, source_file, body, mode, note=note)
    return {'status': mode, 'lines': 0, 'assets': copied}


def render_fallback(existing_html: Path, output_html: Path, title: str, date: str, source_file: str, mode: str) -> dict:
    raw = existing_html.read_text(encoding='utf-8', errors='replace')
    soup = BeautifulSoup(raw, 'html.parser')
    for tag in soup.find_all(['script', 'style']):
        tag.decompose()
    body = soup.body or soup
    header = body.find('header')
    if header:
        header.decompose()
    content = ''.join(str(x) for x in body.contents)
    wrapped = f'<div class="fallback-content">{content}</div>'
    write_page(output_html, title, date, source_file, wrapped, mode, note='Resa editoriale ricostruita dalla trascrizione disponibile; la formattazione originale non era recuperabile integralmente.')
    return {'status': mode, 'lines': 0, 'assets': 0}


def write_page(output_html: Path, title: str, date: str, source_file: str, body: str, mode: str, note: str = '') -> None:
    output_html.parent.mkdir(parents=True, exist_ok=True)
    page = f'''<!doctype html>
<html lang="it">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1,viewport-fit=cover">
<title>{html.escape(title)} · Archivio Fengard</title>
<style>{BASE_CSS}</style>
</head>
<body>
<nav class="archive-bar"><a href="../index.html">← Torna alla rete</a><span>Archivio locale · {html.escape(date or 'data non disponibile')}</span></nav>
<main class="page-wrap">
<article class="source-card" data-render-mode="{html.escape(mode)}">
<header class="source-header"><h1>{html.escape(title)}</h1><div class="source-meta">{html.escape(date or 'Data non disponibile')} · fonte storica: {html.escape(source_file)}</div></header>
<div class="source-body">{body}<div class="render-note">{html.escape(note)}</div></div>
</article>
</main>
</body></html>'''
    output_html.write_text(page, encoding='utf-8')


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument('--site-root', type=Path, required=True)
    parser.add_argument('--archive-root', type=Path, required=True)
    parser.add_argument('--new-topics', type=Path, required=True)
    parser.add_argument('--output-root', type=Path, required=True)
    args = parser.parse_args()

    if args.output_root.exists():
        shutil.rmtree(args.output_root)
    shutil.copytree(args.site_root, args.output_root)
    (args.output_root / 'assets').mkdir(exist_ok=True)

    rows = read_csv(args.new_topics)
    report = []
    temp_root = Path(tempfile.mkdtemp(prefix='fengard-render-'))
    try:
        for index, row in enumerate(rows, start=1):
            source_file = row['source_file']
            source = args.archive_root / source_file
            rel_url = row['topic_url']
            output_html = args.output_root / rel_url
            existing_html = args.site_root / rel_url
            title = row.get('topic_title') or source.stem
            date = row.get('actual_start_date') or row.get('actual_year') or ''
            asset_slug = Path(rel_url).stem
            asset_dir = args.output_root / 'assets' / asset_slug
            suffix = source.suffix.lower()
            try:
                if suffix == '.docx':
                    result = render_docx(source, output_html, asset_dir, title, date, source_file)
                elif suffix == '.doc':
                    result = render_fallback(existing_html, output_html, title, date, source_file, 'legacy-doc-transcription')
                elif suffix in {'.html', '.htm'}:
                    result = render_legacy(source, output_html, asset_dir, title, date, source_file, temp_root)
                    if result['status'] == 'fallback_required':
                        result = render_fallback(existing_html, output_html, title, date, source_file, 'legacy-html-fallback')
                elif suffix == '.pdf':
                    result = render_fallback(existing_html, output_html, title, date, source_file, 'pdf-transcription')
                else:
                    result = render_fallback(existing_html, output_html, title, date, source_file, 'text-transcription')
                status = result['status']
                error = ''
            except Exception as exc:
                result = render_fallback(existing_html, output_html, title, date, source_file, 'error-fallback')
                status = 'error-fallback'
                error = repr(exc)
            report.append({
                'source_file': source_file,
                'topic_url': rel_url,
                'format': suffix,
                'render_status': status,
                'assets_copied': result.get('assets', 0),
                'rendered_lines': result.get('lines', 0),
                'error': error,
            })
            if index == 1 or index % 20 == 0 or index == len(rows):
                print(f'[{index}/{len(rows)}] {source_file} -> {status}', flush=True)
    finally:
        shutil.rmtree(temp_root, ignore_errors=True)

    report_path = args.output_root / 'data' / 'source_render_report.csv'
    with report_path.open('w', encoding='utf-8-sig', newline='') as fh:
        writer = csv.DictWriter(fh, fieldnames=list(report[0]))
        writer.writeheader(); writer.writerows(report)

    # Add method note to README.
    readme = args.output_root / 'README.md'
    previous = readme.read_text(encoding='utf-8', errors='replace') if readme.exists() else ''
    previous += '''\n\n## Fonti locali formattate\n\nLe pagine in `sources/` sono state rigenerate dai documenti originali. Nei DOCX sono conservati colori, dimensioni del testo, blocchi di fato, tiri di dado e immagini incorporate. I vecchi Word sono convertiti tramite LibreOffice; HTML, PDF e TXT usano fallback progressivi documentati in `data/source_render_report.csv`.\n'''
    readme.write_text(previous, encoding='utf-8')

    counts = Counter(r['render_status'] for r in report)
    print('Summary:', dict(counts))
    return 0


if __name__ == '__main__':
    raise SystemExit(main())

import re
import sys
from pathlib import Path


BEGIN_PROOF_RE = re.compile(r'\\begin\{proof\}(\[[^\]]*\])?')
END_PROOF_RE = re.compile(r'\\end\{proof\}')
CREF_RE = re.compile(r'\\[cC]ref\{([^}]*)\}')


def extract_cref_labels(text: str) -> list[str]:
    labels = []
    seen = set()

    for match in CREF_RE.finditer(text):
        label = match.group(1).strip()
        if label and label not in seen:
            seen.add(label)
            labels.append(label)

    return labels


def process_tex(text: str) -> str:
    output = []
    pos = 0

    while True:
        begin_match = BEGIN_PROOF_RE.search(text, pos)
        if not begin_match:
            output.append(text[pos:])
            break

        # Copy everything before this proof
        output.append(text[pos:begin_match.start()])

        # Find the matching \end{proof}
        end_match = END_PROOF_RE.search(text, begin_match.end())
        if not end_match:
            raise ValueError("Found \\begin{proof} without matching \\end{proof}")

        # Extract proof pieces
        begin_proof = text[begin_match.start():begin_match.end()]
        proof_body = text[begin_match.end():end_match.start()]
        end_proof = text[end_match.start():end_match.end()]

        # Collect cref labels from the proof body
        labels = extract_cref_labels(proof_body)

        # Rebuild the proof
        output.append(begin_proof)
        if labels:
            output.append("\n\\uses{" + ",".join(labels) + "}")
        output.append(proof_body)
        output.append(end_proof)

        pos = end_match.end()

    return "".join(output)


def main() -> None:
    if len(sys.argv) != 3:
        print("Usage: python3 make_content.py precontent.tex content.tex")
        sys.exit(1)

    input_path = Path(sys.argv[1])
    output_path = Path(sys.argv[2])

    text = input_path.read_text(encoding="utf-8")
    new_text = process_tex(text)
    output_path.write_text(new_text, encoding="utf-8")

    print(f"Wrote {output_path}")


if __name__ == "__main__":
    main()
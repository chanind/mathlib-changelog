import { FC } from "react";
import ReactMarkdown from "react-markdown";
import remarkGfm from "remark-gfm";

export interface MathlibGithubMarkdownProps {
  contents: string;
}

const linkifyGithubRefs = (contents: string): string =>
  contents.replace(
    /#(\d+)/g,
    "[#$1](https://github.com/leanprover-community/mathlib/pull/$1)"
  );

const MathlibGithubMarkdown: FC<MathlibGithubMarkdownProps> = ({
  contents,
}) => (
  <ReactMarkdown remarkPlugins={[remarkGfm]}>
    {linkifyGithubRefs(contents)}
  </ReactMarkdown>
);

export default MathlibGithubMarkdown;

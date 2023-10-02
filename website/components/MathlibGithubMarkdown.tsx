import { FC } from "react";
import ReactMarkdown from "react-markdown";
import remarkGfm from "remark-gfm";
import { LeanVersion } from "../data/types";

export interface MathlibGithubMarkdownProps {
  contents: string;
  version: LeanVersion;
}

const repoName = (version: LeanVersion): string =>
  version == "v3" ? "mathlib" : "mathlib4";

const linkifyGithubRefs = (contents: string, version: LeanVersion): string =>
  contents.replace(
    /#(\d+)/g,
    `[#$1](https://github.com/leanprover-community/${repoName(
      version
    )}/pull/$1)`
  );

const MathlibGithubMarkdown: FC<MathlibGithubMarkdownProps> = ({
  contents,
  version,
}) => (
  <ReactMarkdown remarkPlugins={[remarkGfm]}>
    {linkifyGithubRefs(contents, version)}
  </ReactMarkdown>
);

export default MathlibGithubMarkdown;

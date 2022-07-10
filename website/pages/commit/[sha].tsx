import { CodeIcon, MinusIcon, PlusIcon } from "@heroicons/react/solid";
import { GetStaticPaths, GetStaticProps, NextPage } from "next";
import Link from "next/link";
import Layout from "../../components/Layout";
import MathlibGithubMarkdown from "../../components/MathlibGithubMarkdown";
import { getCommit } from "../../data/database";
import { ChangeType, CommitData } from "../../data/types";

export const getStaticPaths: GetStaticPaths = () => ({
  paths: [],
  fallback: "blocking",
});

interface CommitProps {
  commit: CommitData;
}

export const getStaticProps: GetStaticProps<CommitProps> = (context) => {
  if (!context.params?.sha || Array.isArray(context.params.sha)) {
    return { notFound: true };
  }
  const commit = getCommit(context.params.sha);
  if (!commit) return { notFound: true };
  return { props: { commit } };
};

const getLabel = (changeType: ChangeType) => {
  if (changeType === "add") {
    return (
      <span className="text-sm text-green-400">
        <PlusIcon className="w-4 h-4 inline" /> added
      </span>
    );
  }
  if (changeType === "del") {
    return (
      <span className="text-sm text-red-400">
        <MinusIcon className="w-4 h-4 inline" /> deleted
      </span>
    );
  }
  return (
    <span className="text-sm text-blue-400">
      <CodeIcon className="w-4 h-4 inline" /> modified
    </span>
  );
};

const Commit: NextPage<CommitProps> = ({ commit }) => {
  return (
    <Layout>
      <h1 className="text-xl">
        <span className="text-gray-400">Commit</span> {commit.sha}
      </h1>
      <a
        href={`https://github.com/leanprover-community/mathlib/commit/${commit.sha}`}
        className="text-blue-600 text-xs"
      >
        View on Github →
      </a>

      <div>
        <MathlibGithubMarkdown contents={commit.message} />
      </div>
      <h4 className="mt-4 mb-2 font-bold text-sm">Estimated changes</h4>
      <div>
        {commit.changes.map((diff, i) => (
          <div className="my-1" key={i}>
            <div>{diff.pathChange}</div>
            <div className="pl-2 text-sm">
              {diff.changes.map(([changeType, itemType, itemName], j) => (
                <div key={j}>
                  <span className="inline-block min-w-[100px] text-right">
                    {getLabel(changeType)}
                  </span>{" "}
                  <span className="font-semibold">{itemType}</span>{" "}
                  <Link href={`/${itemType}/${itemName}`}>
                    <a>{itemName}</a>
                  </Link>
                </div>
              ))}
            </div>
          </div>
        ))}
      </div>
    </Layout>
  );
};

export default Commit;

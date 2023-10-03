import { GetStaticPaths, GetStaticProps, NextPage } from "next";
import { ItemChangeHistory } from "../../../components/ItemChangeHistory";
import Layout from "../../../components/Layout";
import { getInductive } from "../../../data/database";
import { ChangelogItemData } from "../../../data/extractDataFromChangelog";

export const getStaticPaths: GetStaticPaths = () => ({
  paths: [],
  fallback: "blocking",
});

interface InductiveProps {
  inductive: ChangelogItemData;
}

export const getStaticProps: GetStaticProps<InductiveProps> = (context) => {
  if (!context.params?.name || Array.isArray(context.params.name)) {
    return { notFound: true };
  }
  const inductive = getInductive("v3", context.params.name);
  if (!inductive) return { notFound: true };
  return { props: { inductive } };
};

const Inductive: NextPage<InductiveProps> = ({ inductive }) => {
  return (
    <Layout version="v3">
      <h1 className="text-xl">
        <span className="text-gray-400">Inductive</span> {inductive.name}
      </h1>
      <h4 className="text-sm mt-4">Modification history</h4>
      <div>
        <ItemChangeHistory item={inductive} version="v3" />
      </div>
    </Layout>
  );
};

export default Inductive;

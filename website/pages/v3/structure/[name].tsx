import { GetStaticPaths, GetStaticProps, NextPage } from "next";
import { ItemChangeHistory } from "../../../components/ItemChangeHistory";
import Layout from "../../../components/Layout";
import { getStructure } from "../../../data/database";
import { ChangelogItemData } from "../../../data/extractDataFromChangelog";

export const getStaticPaths: GetStaticPaths = () => ({
  paths: [],
  fallback: "blocking",
});

interface StructureProps {
  structure: ChangelogItemData;
}

export const getStaticProps: GetStaticProps<StructureProps> = (context) => {
  if (!context.params?.name || Array.isArray(context.params.name)) {
    return { notFound: true };
  }
  const structure = getStructure("v3", context.params.name);
  if (!structure) return { notFound: true };
  return { props: { structure } };
};

const Structure: NextPage<StructureProps> = ({ structure }) => {
  return (
    <Layout version="v3">
      <h1 className="text-xl">
        <span className="text-gray-400">Structure</span> {structure.name}
      </h1>
      <h4 className="text-sm mt-4">Modification history</h4>
      <div>
        <ItemChangeHistory item={structure} version="v3" />
      </div>
    </Layout>
  );
};

export default Structure;

import { GetStaticPaths, GetStaticProps, NextPage } from "next";
import { ItemChangeHistory } from "../../../components/ItemChangeHistory";
import Layout from "../../../components/Layout";
import { getDef } from "../../../data/database";
import { ChangelogItemData } from "../../../data/extractDataFromChangelog";

export const getStaticPaths: GetStaticPaths = () => ({
  paths: [],
  fallback: "blocking",
});

interface DefProps {
  def: ChangelogItemData;
}

export const getStaticProps: GetStaticProps<DefProps> = (context) => {
  if (!context.params?.name || Array.isArray(context.params.name)) {
    return { notFound: true };
  }
  const def = getDef("v3", context.params.name);
  if (!def) return { notFound: true };
  return { props: { def } };
};

const Def: NextPage<DefProps> = ({ def }) => {
  return (
    <Layout version="v3">
      <h1 className="text-xl">
        <span className="text-gray-400">Def</span> {def.name}
      </h1>
      <h4 className="text-sm mt-4">Modification history</h4>
      <div>
        <ItemChangeHistory item={def} version="v3" />
      </div>
    </Layout>
  );
};

export default Def;

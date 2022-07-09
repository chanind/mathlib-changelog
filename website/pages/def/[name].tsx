import { GetStaticPaths, GetStaticProps, NextPage } from "next";
import { ItemChangeHistory } from "../../components/ItemChangeHistory";
import Layout from "../../components/Layout";
import { getDef, getDefs } from "../../data/database";
import { ChangelogItemData } from "../../data/extractDataFromChangelog";

export const getStaticPaths: GetStaticPaths = () => {
  const defs = getDefs();
  return {
    paths: defs.map(({ name }) => ({
      params: { name },
    })),
    fallback: false,
  };
};

interface DefProps {
  def: ChangelogItemData;
}

export const getStaticProps: GetStaticProps<DefProps> = (context) => {
  if (!context.params?.name || Array.isArray(context.params.name)) {
    return { notFound: true };
  }
  const def = getDef(context.params.name);
  if (!def) return { notFound: true };
  return { props: { def } };
};

const Def: NextPage<DefProps> = ({ def }) => {
  return (
    <Layout>
      <h1 className="text-xl">
        <span className="text-gray-400">Def</span> {def.name}
      </h1>
      <h4 className="text-sm mt-4">Modification history</h4>
      <div className="max-w-md">
        <ItemChangeHistory item={def} />
      </div>
    </Layout>
  );
};

export default Def;

import { GetStaticPaths, GetStaticProps, NextPage } from "next";
import { ItemChangeHistory } from "../../components/ItemChangeHistory";
import Layout from "../../components/Layout";
import { getTheorem, getTheorems } from "../../data/database";
import { ChangelogItemData } from "../../data/extractDataFromChangelog";

export const getStaticPaths: GetStaticPaths = () => {
  const theorems = getTheorems();
  return {
    paths: theorems.map(({ name }) => ({
      params: { name },
    })),
    fallback: false,
  };
};

interface TheoremProps {
  theorem: ChangelogItemData;
}

export const getStaticProps: GetStaticProps<TheoremProps> = (context) => {
  if (!context.params?.name || Array.isArray(context.params.name)) {
    return { notFound: true };
  }
  const theorem = getTheorem(context.params.name);
  if (!theorem) return { notFound: true };
  return { props: { theorem } };
};

const Theorem: NextPage<TheoremProps> = ({ theorem }) => {
  return (
    <Layout>
      <h1 className="text-xl">
        <span className="text-gray-400">Theorem</span> {theorem.name}
      </h1>
      <h4 className="text-sm mt-4">Modification history</h4>
      <div className="max-w-md">
        <ItemChangeHistory item={theorem} />
      </div>
    </Layout>
  );
};

export default Theorem;

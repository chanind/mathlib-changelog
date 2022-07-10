import { GetStaticPaths, GetStaticProps, NextPage } from "next";
import { ItemChangeHistory } from "../../components/ItemChangeHistory";
import Layout from "../../components/Layout";
import { getLemma, getLemmas } from "../../data/database";
import { ChangelogItemData } from "../../data/extractDataFromChangelog";

export const getStaticPaths: GetStaticPaths = () => {
  const lemmas = getLemmas();
  return {
    paths: lemmas.map(({ name }) => ({
      params: { name },
    })),
    fallback: false,
  };
};

interface LemmaProps {
  lemma: ChangelogItemData;
}

export const getStaticProps: GetStaticProps<LemmaProps> = (context) => {
  if (!context.params?.name || Array.isArray(context.params.name)) {
    return { notFound: true };
  }
  const lemma = getLemma(context.params.name);
  if (!lemma) return { notFound: true };
  return { props: { lemma } };
};

const Lemma: NextPage<LemmaProps> = ({ lemma }) => {
  return (
    <Layout>
      <h1 className="text-xl">
        <span className="text-gray-400">Lemma</span> {lemma.name}
      </h1>
      <h4 className="text-sm mt-4">Modification history</h4>
      <div className="max-w-md">
        <ItemChangeHistory item={lemma} />
      </div>
    </Layout>
  );
};

export default Lemma;

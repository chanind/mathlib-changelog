import { GetStaticPaths, GetStaticProps, NextPage } from "next";
import { ItemChangeHistory } from "../../components/ItemChangeHistory";
import Layout from "../../components/Layout";
import { getAbbreviation } from "../../data/database";
import { ChangelogItemData } from "../../data/extractDataFromChangelog";

export const getStaticPaths: GetStaticPaths = () => ({
  paths: [],
  fallback: "blocking",
});

interface AbbreviationProps {
  abbreviation: ChangelogItemData;
}

export const getStaticProps: GetStaticProps<AbbreviationProps> = (context) => {
  if (!context.params?.name || Array.isArray(context.params.name)) {
    return { notFound: true };
  }
  const abbreviation = getAbbreviation(context.params.name);
  if (!abbreviation) return { notFound: true };
  return { props: { abbreviation } };
};

const Abbreviation: NextPage<AbbreviationProps> = ({ abbreviation }) => {
  return (
    <Layout>
      <h1 className="text-xl">
        <span className="text-gray-400">Abbreviation</span> {abbreviation.name}
      </h1>
      <h4 className="text-sm mt-4">Modification history</h4>
      <div>
        <ItemChangeHistory item={abbreviation} />
      </div>
    </Layout>
  );
};

export default Abbreviation;

import type { NextPage } from "next";
import Layout from "../components/Layout";

const Home: NextPage = () => {
  return (
    <Layout>
      <div className="flex flex-wrap">
        <h1 className="text-xl">About</h1>
        <p className="mt-4 text-base leading-relaxed text-gray-800">
          This poject is an auto-updating list of changes from Lean&apos;s{" "}
          <a
            href="https://github.com/leanprover-community/mathlib"
            target="blank"
          >
            Mathlib library
          </a>
          . Mathlib is a powerful repository of math proofs in Lean, but
          there&apos;s no versioning of the library, and breaking changes can
          occur at any time without notice. This project exists as a way to make
          it easier to track down what happened to a theorem or lemma that you
          might be using, but suddenly discover is no longer available.
        </p>
        <p className="mt-4 text-base leading-relaxed text-gray-800">
          This project is far from perfect. While it catches a lot of the
          changes to Lean in each change, this is just an estimate based on the
          git diff of the change, and likely it still misses a lot. If you have
          any ideas for improvements, find any bugs, or have any other comments,
          feel free to open a{" "}
          <a
            href="https://github.com/chanind/mathlib-changelog/issues"
            className="text-blue-600 hover:underline"
          >
            Github issue
          </a>
          .
        </p>
      </div>
    </Layout>
  );
};

export default Home;
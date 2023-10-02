import type { NextPage } from "next";
import Layout from "../components/Layout";

const About: NextPage = () => {
  return (
    <Layout version="v3">
      <div className="flex flex-wrap">
        <h1 className="text-xl">About</h1>
        <p className="mt-4 text-base leading-relaxed text-gray-800">
          This project is an auto-updating list of changes from{" "}
          <a href="https://leanprover.github.io/">Lean</a>&apos;s{" "}
          <a
            href="https://github.com/leanprover-community/mathlib"
            target="blank"
          >
            Mathlib library
          </a>
          . Mathlib is a powerful repository of math proofs in Lean, but
          there&apos;s no versioning of the library, and breaking changes can
          occur at any time without notice. This project exists as a way to make
          it easier to track down what happened to a theorem that you might be
          using, but suddenly discover is no longer available.
        </p>
        <p className="mt-4 text-base leading-relaxed text-gray-800">
          This project is far from perfect. While it should catch most of the
          changes to Mathlib in each commit, it doesn&apos;t run a full Lean and
          Mathlib environment so there&apos;s not guarantee that everything is
          picked up. If you have any ideas for improvements, find any bugs, or
          have any other comments, feel free to open a{" "}
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

export default About;

import type { NextPage } from "next";
import Link from "next/link";
import Layout from "../components/Layout";

const NotFound: NextPage = () => {
  return (
    <Layout>
      <div className="text-center pt-10">
        <h1 className="text-6xl mt-20">404</h1>
        <p className="text-gray-600 mb-10">Page not found</p>
        <Link href="/">
          <a className="rounded-md py-2 px-4 bg-blue-600 text-white">
            Go back home
          </a>
        </Link>
      </div>
    </Layout>
  );
};

export default NotFound;

import Link from "next/link";
import Head from "next/head";
import { FC, ReactNode } from "react";
import HeaderNav from "../components/HeaderNav";
import { LeanVersion } from "../data/types";

interface LayoutProps {
  children: ReactNode;
  version: LeanVersion;
}

const Layout: FC<LayoutProps> = ({ children, version }) => {
  return (
    <div>
      <Head>
        <title>Mathlib Changlelog {version}</title>
        <meta
          name="description"
          content="Mathlib Changelog - Changes List for Lean Mathlib"
        />
        <link rel="icon" href="/favicon.ico" />
      </Head>

      <HeaderNav version={version} />
      {version == "v3" && (
        <div className="text-center p-3 bg-gray-200">
          Mathlib v3 is deprecated. <Link href="/v4/">Go to Mathlib v4</Link>
        </div>
      )}
      <main className="container mt-4 mx-auto px-2">{children}</main>
    </div>
  );
};

export default Layout;

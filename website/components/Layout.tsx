import Head from "next/head";
import { FC, ReactNode } from "react";
import HeaderNav from "../components/HeaderNav";
import { LeanVersion } from "../data/types";

interface LayoutProps {
  children: ReactNode;
  version: LeanVersion;
  banner?: ReactNode;
}

const Layout: FC<LayoutProps> = ({ children, version, banner }) => {
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
      {banner}
      <main className="container mt-4 mx-auto px-2">{children}</main>
    </div>
  );
};

export default Layout;

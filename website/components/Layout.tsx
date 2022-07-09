import Head from 'next/head';
import { FC, ReactNode } from 'react';
import HeaderNav from '../components/HeaderNav';

interface LayoutProps {
  children: ReactNode;
}

const Layout: FC<LayoutProps> = ({ children }) => {
  return (
    <div>
      <Head>
        <title>Mathlib Changlelog</title>
        <meta
          name="description"
          content="Mathlib Changlelog - Changes List for Lean Mathlib"
        />
        <link rel="icon" href="/favicon.ico" />
      </Head>

      <HeaderNav />
      <main className="container mt-4 mx-auto px-2">{children}</main>
    </div>
  );
};

export default Layout;

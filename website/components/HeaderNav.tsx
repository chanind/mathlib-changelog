import Link from "next/link";
import { LeanVersion } from "../data/types";
import versionPrefix from "../util/versionPrefix";
import { FC } from "react";

export interface HeaderNavProps {
  version: LeanVersion;
}

const HeaderNav: FC<HeaderNavProps> = ({ version }) => (
  <nav className="flex items-center justify-between flex-wrap bg-gray-800 py-4 sm:p-4">
    <Link href={`${versionPrefix(version)}/`}>
      <div className="flex items-center flex-no-shrink mr-6 cursor-pointer ml-2">
        <span className="font-semibold text-md sm:text-xl tracking-tight text-white">
          Mathlib Changelog{" "}
          <span className="font-normal text-gray-400">{version}</span>
        </span>
      </div>
    </Link>
    <div className="w-full flex items-center w-auto">
      <div className="text-sm flex-grow">
        <Link href={`${versionPrefix(version)}/changelog/1`}>
          <a className="block mt-4 inline-block mt-0 text-gray-200 hover:text-white mx-2">
            Changelog
          </a>
        </Link>
        <Link href={`${versionPrefix(version)}/about`}>
          <a className="block mt-4 inline-block mt-0 text-gray-200 hover:text-white mx-2">
            About
          </a>
        </Link>
        <a
          href="https://github.com/chanind/mathlib-changelog"
          className="block mt-4 inline-block mt-0 text-gray-200 hover:text-white mx-2"
        >
          Github
        </a>
      </div>
    </div>
  </nav>
);

export default HeaderNav;

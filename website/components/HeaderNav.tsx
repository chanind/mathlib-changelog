import Link from "next/link";

const HeaderNav = () => (
  <nav className="flex items-center justify-between flex-wrap bg-gray-800 py-4 sm:p-4">
    <Link href="/">
      <div className="flex items-center flex-no-shrink mr-6 cursor-pointer ml-2">
        <span className="font-semibold text-xl tracking-tight text-white">
          Mathlib Changelog
        </span>
      </div>
    </Link>
    <div className="w-full flex items-center w-auto">
      <div className="text-sm flex-grow">
        <Link href="/changelog/1">
          <a className="block mt-4 inline-block mt-0 text-gray-200 hover:text-white mx-2">
            Changelog
          </a>
        </Link>
        <Link href="/about">
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

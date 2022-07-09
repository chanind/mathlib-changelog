import Link from "next/link";

const HeaderNav = () => (
  <nav className="flex items-center justify-between flex-wrap bg-gray-800 py-4 sm:p-4">
    <Link href="/">
      <div className="flex items-center flex-no-shrink mr-6 cursor-pointer">
        <svg
          className="h-8 w-8 mr-2"
          width="54"
          height="54"
          viewBox="0 0 54 54"
          xmlns="http://www.w3.org/2000/svg"
        >
          <path
            fill="white"
            d="M13.5 22.1c1.8-7.2 6.3-10.8 13.5-10.8 10.8 0 12.15 8.1 17.55 9.45 3.6.9 6.75-.45 9.45-4.05-1.8 7.2-6.3 10.8-13.5 10.8-10.8 0-12.15-8.1-17.55-9.45-3.6-.9-6.75.45-9.45 4.05zM0 38.3c1.8-7.2 6.3-10.8 13.5-10.8 10.8 0 12.15 8.1 17.55 9.45 3.6.9 6.75-.45 9.45-4.05-1.8 7.2-6.3 10.8-13.5 10.8-10.8 0-12.15-8.1-17.55-9.45-3.6-.9-6.75.45-9.45 4.05z"
          />
        </svg>
        <span className="font-semibold text-xl tracking-tight text-white">
          Mathlib Changelog
        </span>
      </div>
    </Link>
    <div className="w-full flex items-center w-auto">
      <div className="text-sm flex-grow">
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

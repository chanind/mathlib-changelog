// This is hacky, but I can't import typescript database in here
// and the sitemap apparently only works with plain JS :/
// NOTE: `yarn build:search` must be run before the sitemap can be generated

const searchItems = require("./public/searchItems.json");

const itemTypesMap = {
  d: "def",
  t: "theorem",
  i: "inductive",
  s: "structure",
};

module.exports = {
  siteUrl: process.env.SITE_URL || "https://mathlib-changelog.org",
  generateRobotsTxt: true, // (optional)
  additionalPaths: async (config) =>
    searchItems.map((item) => {
      const fullName = item.replace(/^[a-z]+:/i, "");
      return { loc: `/${itemTypesMap[item[0]]}/${fullName}` };
    }),
};

import { get, keyBy, memoize, set } from "lodash";
import {
  ChangelogItemData,
  extractDefsData,
  extractItemsData,
  extractLemmasData,
  extractTheoremsData,
} from "./extractDataFromChangelog";
import loadCommitData from "./loadCommitData";
import { CommitData } from "./types";

/**
 * Data lookup methods
 * NOTE: These should only be called during static site generation!
 */

export const getItems = memoize(() => extractItemsData(loadCommitData()));
export const getLemmas = memoize(() => extractLemmasData(loadCommitData()));
export const getTheorems = memoize(() => extractTheoremsData(loadCommitData()));
export const getDefs = memoize(() => extractDefsData(loadCommitData()));
export const getCommits = memoize(() => loadCommitData().commits);

interface ItemsLookupTable {
  [itemType: string]: { [itemName: string]: ChangelogItemData };
}

const getItemsLookupTable: () => ItemsLookupTable = memoize(() => {
  const itemsData = extractItemsData(loadCommitData());
  const lookupTable: ItemsLookupTable = {};
  for (const item of itemsData) {
    set(lookupTable, [item.type, item.name], item);
  }
  return lookupTable;
});

interface CommitsLookupTable {
  [sha: string]: CommitData;
}
const geCommitsLookupTable: () => CommitsLookupTable = memoize(() => {
  const commits = getCommits();
  return {
    ...keyBy(commits, "sha"),
    ...keyBy(commits, (commit) => commit.sha.slice(0, 7)),
  };
});

export const getLemma = (name: string) =>
  get(getItemsLookupTable(), ["lemma", name]);

export const getTheorem = (name: string) =>
  get(getItemsLookupTable(), ["theorem", name]);

export const getDef = (name: string) =>
  get(getItemsLookupTable(), ["def", name]);

export const getCommit = (sha: string) => geCommitsLookupTable()[sha];

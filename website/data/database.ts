import { createHash } from "crypto";
import { get, keyBy, memoize, set } from "lodash";
import {
  ChangelogItemData,
  extractAbbreviationsData,
  extractDefsData,
  extractInductivesData,
  extractItemsData,
  extractLemmasData,
  extractStructuresData,
  extractTheoremsData,
} from "./extractDataFromChangelog";
import loadRawCommitData from "./loadRawCommitData";
import { ChangelogData, CommitData } from "./types";

/**
 * Data lookup methods
 * NOTE: These should only be called during static site generation!
 */

const loadCommitData = memoize(
  (): ChangelogData => ({
    commits: loadRawCommitData().commits.map((rawCommit) => ({
      ...rawCommit,
      changes: rawCommit.changes.map((rawChange) => ({
        ...rawChange,
        pathSha: createHash("sha256")
          .update(rawChange.newPath || rawChange.oldPath || "")
          .digest("hex"),
      })),
    })),
  })
);

export const getItems = memoize(() => extractItemsData(loadCommitData()));
export const getLemmas = memoize(() => extractLemmasData(loadCommitData()));
export const getTheorems = memoize(() => extractTheoremsData(loadCommitData()));
export const getInductives = memoize(() =>
  extractInductivesData(loadCommitData())
);
export const getDefs = memoize(() => extractDefsData(loadCommitData()));
export const getStructures = memoize(() =>
  extractStructuresData(loadCommitData())
);
export const getAbbreviations = memoize(() =>
  extractAbbreviationsData(loadCommitData())
);
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
const getCommitsLookupTable: () => CommitsLookupTable = memoize(() => {
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

export const getStructure = (name: string) =>
  get(getItemsLookupTable(), ["structure", name]);

export const getAbbreviation = (name: string) =>
  get(getItemsLookupTable(), ["abbreviation", name]);

export const getInductive = (name: string) =>
  get(getItemsLookupTable(), ["inductive", name]);

export const getCommit = (sha: string) => getCommitsLookupTable()[sha];

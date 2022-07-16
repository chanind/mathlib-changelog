import { createHash } from "crypto";
import { get, set } from "lodash";
import summarizeHeadline from "../util/summarizeHeadline";
import { ChangelogData, ChangeType, ItemType } from "./types";

export interface ChangelogItemData {
  name: string;
  type: ItemType;
  history: ChangelogItemEvent[];
}

export interface ChangelogItemEvent {
  commitHeadline: string;
  commitTimestamp: number;
  commitSha: String;
  diffPath: string;
  diffPathSha: string;
  type: ChangeType;
}

export const extractItemsData = (
  changelog: ChangelogData
): ChangelogItemData[] => {
  const itemsHistoryMapping: {
    [itemType: string]: { [itemName: string]: ChangelogItemEvent[] };
  } = {};

  for (const commit of changelog.commits) {
    for (const diff of commit.changes) {
      for (const change of diff.changes) {
        const [changeType, itemType, itemName, namespace] = change;
        const history = get(itemsHistoryMapping, [itemType, itemName], []);
        const diffPath = (diff.newPath || diff.oldPath) as string;
        const item: ChangelogItemEvent = {
          diffPath,
          diffPathSha: diff.pathSha,
          commitHeadline: summarizeHeadline(commit.message),
          commitTimestamp: commit.timestamp,
          commitSha: commit.sha,
          type: changeType,
        };
        const fullName = [...namespace, itemName].join(".");
        set(itemsHistoryMapping, [itemType, fullName], [...history, item]);
      }
    }
  }
  const itemsData: ChangelogItemData[] = [];
  for (const [itemType, itemNamesMapping] of Object.entries(
    itemsHistoryMapping
  )) {
    for (const [itemName, history] of Object.entries(itemNamesMapping)) {
      itemsData.push({
        name: itemName,
        type: itemType as ItemType,
        history,
      });
    }
  }
  return itemsData;
};

export const extractLemmasData = (
  changelog: ChangelogData
): ChangelogItemData[] =>
  extractItemsData(changelog).filter((item) => item.type === "lemma");

export const extractTheoremsData = (
  changelog: ChangelogData
): ChangelogItemData[] =>
  extractItemsData(changelog).filter((item) => item.type === "theorem");

export const extractDefsData = (
  changelog: ChangelogData
): ChangelogItemData[] =>
  extractItemsData(changelog).filter((item) => item.type === "def");

export const extractAbbreviationsData = (
  changelog: ChangelogData
): ChangelogItemData[] =>
  extractItemsData(changelog).filter((item) => item.type === "abbreviation");

export const extractStructuresData = (
  changelog: ChangelogData
): ChangelogItemData[] =>
  extractItemsData(changelog).filter((item) => item.type === "structure");

export const extractInductivesData = (
  changelog: ChangelogData
): ChangelogItemData[] =>
  extractItemsData(changelog).filter((item) => item.type === "inductive");

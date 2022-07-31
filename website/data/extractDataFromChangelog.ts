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
        const diffPath = (diff.newPath || diff.oldPath) as string;

        const fullName = [...namespace, itemName].join(".");
        const history = get(itemsHistoryMapping, [itemType, fullName], []);
        const lastChange = history[history.length - 1];
        if (lastChange && lastChange.commitSha === commit.sha) {
          // if there are 2 different conflicting changes to the same item in the same commit, it's a modification
          if (lastChange.type !== changeType) {
            lastChange.type = "mod";
          }
        } else {
          const item: ChangelogItemEvent = {
            diffPath,
            diffPathSha: diff.pathSha,
            commitHeadline: summarizeHeadline(commit.message),
            commitTimestamp: commit.timestamp,
            commitSha: commit.sha,
            type: changeType,
          };
          set(itemsHistoryMapping, [itemType, fullName], [...history, item]);
        }
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

export const extractTheoremsData = (
  changelog: ChangelogData
): ChangelogItemData[] =>
  extractItemsData(changelog).filter((item) => item.type === "theorem");

export const extractDefsData = (
  changelog: ChangelogData
): ChangelogItemData[] =>
  extractItemsData(changelog).filter((item) => item.type === "def");

export const extractStructuresData = (
  changelog: ChangelogData
): ChangelogItemData[] =>
  extractItemsData(changelog).filter((item) => item.type === "structure");

export const extractInductivesData = (
  changelog: ChangelogData
): ChangelogItemData[] =>
  extractItemsData(changelog).filter((item) => item.type === "inductive");

import { get, set } from "lodash";
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
        const [changeType, itemType, itemName] = change;
        const history = get(itemsHistoryMapping, [itemType, itemName], []);
        const item: ChangelogItemEvent = {
          commitHeadline: commit.message.split(/\n/)[0].trim(),
          commitTimestamp: commit.timestamp,
          commitSha: commit.sha,
          diffPath: diff.path,
          type: changeType,
        };
        set(itemsHistoryMapping, [itemType, itemName], [...history, item]);
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

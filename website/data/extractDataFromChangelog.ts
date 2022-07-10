import { get, set } from "lodash";
import {
  ChangelogData,
  ChangeType,
  CommitData,
  DiffData,
  ItemType,
} from "./types";

export interface ChangelogItemData {
  name: string;
  type: ItemType;
  history: ChangelogItemEvent[];
}

export interface ChangelogItemEvent {
  commit: CommitData;
  diff: DiffData;
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
        set(
          itemsHistoryMapping,
          [itemType, itemName],
          [...history, { commit, diff, type: changeType }]
        );
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

import { memoize } from "lodash";
import MiniSearch, { SearchResult } from "minisearch";
import { ItemType, LeanVersion } from "./types";

const SEARCH_ITEMS_JSON_URL_V3 = "/searchItems.v3.json";
const SEARCH_ITEMS_JSON_URL_V4 = "/searchItems.v4.json";

export interface SearchableItemDoc {
  id: string;
  name: string;
  fullName: string;
  type: ItemType;
}

const rehydrateExportedSearchItems = (
  exportedItems: string[]
): SearchableItemDoc[] => {
  const itemTypesMap: { [key: string]: ItemType } = {
    d: "def",
    t: "theorem",
    i: "inductive",
    s: "structure",
  };
  return exportedItems.map((item) => {
    const fullName = item.replace(/^[a-z]+:/i, "");
    const nameParts = fullName.split(".");
    const name = nameParts[nameParts.length - 1];
    return {
      name,
      fullName,
      id: item,
      type: itemTypesMap[item[0]],
    };
  });
};

export const createSearch = (): MiniSearch<SearchableItemDoc> =>
  new MiniSearch({
    fields: ["name", "type", "fullName"],
    storeFields: ["type", "fullName"],
    searchOptions: {
      boost: { name: 2 },
      prefix: true,
      weights: { prefix: 0.3, fuzzy: 0.3 },
      boostDocument: (doc, term) => 1 / doc.length + 1 / term.length,
    },
  });

export const populateSearch = (
  search: MiniSearch<SearchableItemDoc>,
  exportedItems: string[]
) => {
  const docs = rehydrateExportedSearchItems(exportedItems);
  search.addAll(docs);
};

export const loadAndPopulateSearch = memoize(async (version: LeanVersion) => {
  const search = createSearch();
  const searchItemsJsonUrl =
    version === "v3" ? SEARCH_ITEMS_JSON_URL_V3 : SEARCH_ITEMS_JSON_URL_V4;
  const exportedSearchItems: string[] = await fetch(searchItemsJsonUrl).then(
    (res) => res.json()
  );
  populateSearch(search, exportedSearchItems);
  return search;
});

export const searchForQuery = async (
  query: string,
  version: LeanVersion
): Promise<(SearchResult & SearchableItemDoc)[]> => {
  const search = await loadAndPopulateSearch(version);
  // need to cast to any here, since TS doesn't know about the actual docs being returned
  return search.search(query) as any[];
};

import { uniq } from "lodash";
import { getItems } from "./database";
import { LeanVersion } from "./types";

const exportItemsForSearch = (version: LeanVersion): string[] => {
  const items = getItems(version);
  return uniq(
    items
      .filter(({ name }) => !name.match(/\{/) && name.match(/[a-z]/gi))
      .map((item) => `${item.type[0]}:${item.name}`)
      .sort()
  );
};

export default exportItemsForSearch;

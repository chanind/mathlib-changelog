import { uniq } from "lodash";
import { getItems } from "./database";

const exportItemsForSearch = (): string[] => {
  const items = getItems();
  return uniq(
    items
      .filter(({ name }) => !name.match(/\{/) && name.match(/[a-z]/gi))
      .map((item) => `${item.type[0]}:${item.name}`)
      .sort()
  );
};

export default exportItemsForSearch;

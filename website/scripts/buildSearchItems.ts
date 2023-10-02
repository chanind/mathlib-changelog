import path from "path";
import { cwd } from "node:process";
import { writeFileSync } from "fs";
import exportItemsForSearch from "../data/exportItemsForSearch";

const ITEMS_FILE_V3 = path.join(cwd(), "public/searchItems.v3.json");
const ITEMS_FILE_V4 = path.join(cwd(), "public/searchItems.v4.json");

const buildSearchItems = () => {
  const itemsV3 = exportItemsForSearch("v3");
  writeFileSync(ITEMS_FILE_V3, JSON.stringify(itemsV3));
  const itemsV4 = exportItemsForSearch("v4");
  writeFileSync(ITEMS_FILE_V4, JSON.stringify(itemsV4));
};

if (require.main === module) {
  buildSearchItems();
}

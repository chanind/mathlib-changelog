import path from "path";
import { cwd } from "node:process";
import { writeFileSync } from "fs";
import exportItemsForSearch from "../data/exportItemsForSearch";

const ITEMS_FILE = path.join(cwd(), "public/searchItems.json");

const buildSearchItems = () => {
  const items = exportItemsForSearch();
  writeFileSync(ITEMS_FILE, JSON.stringify(items));
};

if (require.main === module) {
  buildSearchItems();
}

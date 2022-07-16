import { readFileSync } from "fs";
import { cwd } from "node:process";
import path from "path";
import { RawChangelogData } from "./types";

const COMMIT_DATA_JSON_FILE = path.join(cwd(), "../CHANGELOG.full.json");

const loadRawCommitData = (): RawChangelogData =>
  JSON.parse(readFileSync(COMMIT_DATA_JSON_FILE, "utf-8"));

export default loadRawCommitData;

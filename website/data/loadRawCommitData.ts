import { readFileSync } from "fs";
import { cwd } from "node:process";
import path from "path";
import { LeanVersion, RawChangelogData } from "./types";

const COMMIT_DATA_JSON_FILE_V3 = path.join(cwd(), "../CHANGELOG.v3.full.json");
const COMMIT_DATA_JSON_FILE_V4 = path.join(cwd(), "../CHANGELOG.v4.full.json");

const loadRawCommitData = (version: LeanVersion): RawChangelogData => {
  const dataJson =
    version === "v3" ? COMMIT_DATA_JSON_FILE_V3 : COMMIT_DATA_JSON_FILE_V4;
  return JSON.parse(readFileSync(dataJson, "utf-8"));
};

export default loadRawCommitData;

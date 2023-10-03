import { LeanVersion } from "../data/types";

const versionPrefix = (version: LeanVersion) =>
  version === "v4" ? "/v4" : "/v3";

export default versionPrefix;

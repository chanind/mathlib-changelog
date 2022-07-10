export interface ChangelogData {
  commits: CommitData[];
}

export interface CommitData {
  timestamp: number;
  sha: string;
  message: string;
  changes: DiffData[];
}

export type ChangeType = "mod" | "add" | "del";
export type ItemType = "theorem" | "lemma" | "def";

export interface DiffData {
  pathChange: string;
  path: string;
  changes: [ChangeType, ItemType, string][];
}

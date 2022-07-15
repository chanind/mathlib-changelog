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
  oldPath: string | null;
  newPath: string | null;
  changes: [ChangeType, ItemType, string, string[]][];
}

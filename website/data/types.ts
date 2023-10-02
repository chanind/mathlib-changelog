export interface RawChangelogData {
  commits: RawCommitData[];
}
export interface ChangelogData {
  commits: CommitData[];
}

export interface RawCommitData {
  timestamp: number;
  sha: string;
  message: string;
  changes: RawDiffData[];
}
export interface CommitData extends RawCommitData {
  changes: DiffData[];
}

export type ChangeType = "mod" | "add" | "del";
export type ItemType = "theorem" | "def" | "inductive" | "structure";

export interface RawDiffData {
  oldPath: string | null;
  newPath: string | null;
  changes: [ChangeType, ItemType, string, string[]][];
}
export interface DiffData extends RawDiffData {
  pathSha: string;
}

export type LeanVersion = "v3" | "v4";

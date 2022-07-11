import Link from "next/link";
import { FC } from "react";
import { ChangelogItemData } from "../data/extractDataFromChangelog";
import { PlusIcon, MinusIcon, CodeIcon } from "@heroicons/react/solid";
import { ChangeType } from "../data/types";
import formatTimestamp from "../util/formatTimestamp";

export interface ChangeHistoryProps {
  item: ChangelogItemData;
}

const getLabel = (changeType: ChangeType) => {
  if (changeType === "add") {
    return (
      <span className="text-sm text-green-600">
        <PlusIcon className="w-4 h-4 inline" /> Added
      </span>
    );
  }
  if (changeType === "del") {
    return (
      <span className="text-sm text-red-600">
        <MinusIcon className="w-4 h-4 inline" /> Deleted
      </span>
    );
  }
  return (
    <span className="text-sm text-blue-600">
      <CodeIcon className="w-4 h-4 inline" /> Modified
    </span>
  );
};

export const ItemChangeHistory: FC<ChangeHistoryProps> = ({ item }) => (
  <div>
    <div className="py-2 flex flex-col">
      {item.history.map((event, i) => (
        <Link href={`/commit/${event.commitSha}`} key={i}>
          <a className="p-2 border border-gray-200 my-1 rounded-md hover:border-gray-400 transition text-gray-800">
            <div className="pb-1">
              <span className="text-blue-600">
                {formatTimestamp(event.commitTimestamp)}
              </span>
            </div>
            <div className="text-gray-400 pb-2 text-xs">{event.diffPath}</div>
            <div className="text-gray-800 text-sm pl-2 border-l border-right italic mb-2 truncate">
              {event.commitHeadline}
            </div>
            {getLabel(event.type)} {item.name}
          </a>
        </Link>
      ))}
    </div>
  </div>
);

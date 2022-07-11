import classNames from "classnames";
import { FC, ReactNode } from "react";

export interface PillProps {
  children: ReactNode;
  color: "blue" | "red" | "white" | "black";
}

const Pill: FC<PillProps> = ({ children, color }) => (
  <span
    className={classNames("text-xs inline-block px-1 uppercase rounded-sm", {
      "bg-gray-200": color === "white",
      "text-gray-800": color === "white",
      "bg-gray-800": color === "black",
      "text-gray-400": color === "black",
      "bg-blue-100": color === "blue",
      "text-blue-600": color === "blue",
      "bg-red-200": color === "red",
      "text-red-600": color === "red",
    })}
  >
    {children}
  </span>
);

export default Pill;

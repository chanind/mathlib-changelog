import type { NextPage } from "next";
import { useState } from "react";
import { useRouter } from "next/router";
import classNames from "classnames";
import Autosuggest from "react-autosuggest";
import { useQuery } from "react-query";
import Layout from "../components/Layout";
import Spinner from "../components/Spinner";
import { loadAndPopulateSearch, searchForQuery } from "../data/search";
import Link from "next/link";

if (typeof window !== "undefined") {
  // start loading search data early, so it's ready faster
  loadAndPopulateSearch();
}

const Home: NextPage = () => {
  const [query, setQuery] = useState("");
  const [isNavigating, setIsNavigating] = useState(false);
  const router = useRouter();
  const hasQuery = query.trim() !== "";
  const { data, isLoading } = useQuery(query, async () => {
    if (!hasQuery) return [];
    return searchForQuery(query);
  });

  return (
    <Layout>
      <div className="flex flex-wrap flex-col items-center text-center w-full">
        {isNavigating ? (
          <div className="w-[100px] pt-10">
            <Spinner size={10} />
          </div>
        ) : (
          <>
            <h1 className="text-4xl mt-4 mb-2">Mathlib Changelog</h1>
            <p className="mb-10 text-sm text-gray-400">
              Unofficial change tracker for Lean Mathlib
            </p>
            <Autosuggest
              inputProps={{
                placeholder: "Enter a lemma, theorem, def, or structure",
                className:
                  "p-2 border border-gray-800 display-block md:w-[500px] w-full rounded-sm",
                value: query,
                onChange: (evt: any) => setQuery(evt.target.value),
              }}
              getSuggestionValue={(suggestion) =>
                `${suggestion.type}:${suggestion.fullName}`
              }
              renderSuggestion={(suggestion) => (
                <Link href={`/${suggestion.type}/${suggestion.fullName}`}>
                  <a className="text-gray-800">
                    <span className="text-gray-400 min-w-[70px] inline-block text-right pr-1">
                      {suggestion.type}
                    </span>{" "}
                    {suggestion.fullName}
                  </a>
                </Link>
              )}
              suggestions={(data ?? []).slice(0, 100)}
              onSuggestionsFetchRequested={({ value, reason }) => {
                if (reason === "suggestion-selected") {
                  const type = value.replace(/:.*/, "");
                  const name = value.replace(/^[^:]*:/, "");
                  router.push(`/${type}/${name}`);
                  setQuery("");
                  setIsNavigating(true);
                }
              }}
              onSuggestionsClearRequested={() => setQuery(query)}
              alwaysRenderSuggestions={true}
              theme={{
                suggestionsContainer: classNames(
                  "text-left border border-gray-300 border-t-0 md:w-[500px] w-full mx-auto max-h-[300px] md:max-h-[500px] overflow-y-scroll overflow-x-hidden",
                  {
                    "border-0": (data ?? []).length === 0,
                  }
                ),
                suggestionsList: "list-none pl-0",
                suggestionHighlighted: "bg-blue-200",
                suggestionFirst: "border-t-0",
                suggestion: "border-t p-2 cursor-pointer truncate",
                container: "w-full",
              }}
              renderInputComponent={(inputProps) => (
                <div className="relative">
                  <input {...inputProps} />
                  {hasQuery && isLoading && (
                    <div className="absolute top-0 right-0 bottom-0 flex items-center">
                      <Spinner size={8} />
                    </div>
                  )}
                </div>
              )}
            />
          </>
        )}
      </div>
    </Layout>
  );
};

export default Home;

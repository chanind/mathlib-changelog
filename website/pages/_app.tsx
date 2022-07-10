import "../styles/globals.css";
import type { AppProps } from "next/app";
import { QueryClient, QueryClientProvider } from "react-query";
import { loadAndPopulateSearch } from "../data/search";

const queryClient = new QueryClient();

if (typeof window !== "undefined") {
  // start loading search data early, so it's ready faster
  loadAndPopulateSearch();
}

function MyApp({ Component, pageProps }: AppProps) {
  return (
    <QueryClientProvider client={queryClient}>
      <Component {...pageProps} />
    </QueryClientProvider>
  );
}

export default MyApp;

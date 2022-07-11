const formatTimestamp = (timestamp: number): string =>
  new Date(timestamp * 1000)
    .toISOString()
    .replace("T", " ")
    .replace(/:[^:]*$/, "");

export default formatTimestamp;

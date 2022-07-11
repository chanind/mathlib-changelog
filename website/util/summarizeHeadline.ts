const summarizeHeadline = (text: string): string => {
  const lines = text.trim().split(/\n/);
  const headline = lines[0].trim();
  return lines.length === 1 ? headline : headline + " …";
};

export default summarizeHeadline;

import { ChevronLeftIcon, ChevronRightIcon } from "@heroicons/react/solid";
import { FC } from "react";
import ReactPaginate from "react-paginate";

// modified from https://tailwindui.com/components/application-ui/navigation/pagination

export interface PaginationProps {
  pageNum: number;
  maxPage: number;
  totalResults: number;
  pageStartItemNum: number;
  pageEndItemNum: number;
  onChangePage: (pageNum: number) => void;
}

const Pagination: FC<PaginationProps> = ({
  pageNum,
  maxPage,
  totalResults,
  pageStartItemNum,
  pageEndItemNum,
  onChangePage,
}) => (
  <div className="bg-white py-3 flex items-center justify-between">
    <div className="flex-1 flex items-center justify-between">
      <div className="md:block hidden">
        <p className="text-sm text-gray-500">
          Showing{" "}
          <span className="font-medium text-gray-700">{pageStartItemNum}</span>{" "}
          to <span className="font-medium text-gray-700">{pageEndItemNum}</span>{" "}
          of <span className="font-medium text-gray-700">{totalResults}</span>{" "}
          results
        </p>
      </div>
      <div className="hidden sm:block">
        <ReactPaginate
          breakLabel="..."
          onPageChange={({ selected }) => onChangePage(selected + 1)}
          pageRangeDisplayed={3}
          pageCount={maxPage}
          marginPagesDisplayed={1}
          nextLabel={
            <>
              <span className="sr-only">Next</span>
              <ChevronRightIcon className="h-5 w-5" />
            </>
          }
          previousLabel={
            <>
              <ChevronLeftIcon className="h-5 w-5" />
              <span className="sr-only">Previous</span>
            </>
          }
          forcePage={pageNum - 1}
          activeLinkClassName="z-10 bg-indigo-50 border-indigo-500 text-indigo-600"
          className="list-none p-0 relative z-0 inline-flex rounded-md shadow-sm -space-x-px"
          pageLinkClassName="select-none bg-white border-gray-300 text-gray-500 hover:bg-gray-50 relative inline-flex items-center px-4 py-2 border text-sm font-medium"
          breakLinkClassName="relative inline-flex items-center px-4 py-2 border border-gray-300 bg-white text-sm font-medium text-gray-700"
          previousLinkClassName="relative inline-flex items-center px-2 py-2 rounded-l-md border border-gray-300 bg-white text-sm font-medium text-gray-500 hover:bg-gray-50"
          nextLinkClassName="relative inline-flex items-center px-2 py-2 rounded-r-md border border-gray-300 bg-white text-sm font-medium text-gray-500 hover:bg-gray-50"
          disabledLinkClassName="hover:bg-white cursor-default"
        />
      </div>
      <div className="sm:hidden">
        <ReactPaginate
          breakLabel="..."
          onPageChange={({ selected }) => onChangePage(selected + 1)}
          pageRangeDisplayed={1}
          pageCount={maxPage}
          marginPagesDisplayed={1}
          nextLabel={
            <>
              <span className="sr-only">Next</span>
              <ChevronRightIcon className="h-5 w-5" />
            </>
          }
          previousLabel={
            <>
              <ChevronLeftIcon className="h-5 w-5" />
              <span className="sr-only">Previous</span>
            </>
          }
          forcePage={pageNum - 1}
          activeLinkClassName="z-10 bg-indigo-50 border-indigo-500 text-indigo-600"
          className="list-none p-0 relative z-0 inline-flex rounded-md shadow-sm -space-x-px"
          pageLinkClassName="select-none bg-white border-gray-300 text-gray-500 hover:bg-gray-50 relative inline-flex items-center px-4 py-2 border text-sm font-medium"
          breakLinkClassName="relative inline-flex items-center px-4 py-2 border border-gray-300 bg-white text-sm font-medium text-gray-700"
          previousLinkClassName="relative inline-flex items-center px-2 py-2 rounded-l-md border border-gray-300 bg-white text-sm font-medium text-gray-500 hover:bg-gray-50"
          nextLinkClassName="relative inline-flex items-center px-2 py-2 rounded-r-md border border-gray-300 bg-white text-sm font-medium text-gray-500 hover:bg-gray-50"
          disabledLinkClassName="hover:bg-white cursor-default"
        />
      </div>
    </div>
  </div>
);

export default Pagination;

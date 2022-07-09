from datetime import datetime


def format_datetime(dt: datetime) -> str:
    return dt.isoformat().replace("T", " ").replace("+00:00", "")

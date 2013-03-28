package z3;

public final class DefaultErrorHandler {

    // errorCode description:
    //  0 -- OK
    //  1 -- sort error
    //  2 -- index out of bounds
    //  3 -- invalid arg
    //  4 -- parser error
    //  5 -- no parser
    //  6 -- invalid pattern
    //  7 -- memout fail
    //  8 -- file access error
    //  9 -- internal fatal
    // 10 -- invalid usage
    // 11 -- dec ref error
    public void handleError(int errorCode) {
        String msg;
        switch(errorCode) {
            case  0 : msg = "OK"; break;
            case  1 : msg = "Sort error"; break;
            case  2 : msg = "Index out of bounds"; break;
            case  3 : msg = "Invalid argument"; break;
            case  4 : msg = "Parser error"; break;
            case  5 : msg = "No parser"; break;
            case  6 : msg = "Invalid pattern"; break;
            case  7 : msg = "Memout fail error"; break;
            case  8 : msg = "File access error"; break;
            case  9 : msg = "Internal fatal error"; break;
            case 10 : msg = "Invalid usage"; break;
            case 11 : msg = "Dec. ref. error"; break;
            default : msg = "Unknown error"; break;
        }

        int errCode;
        if(errorCode >= 0 && errorCode <= 11) {
            errCode = errorCode;
        } else {
            errCode = -1;
        }

        throw new Z3ErrorException(errCode, msg);
    }
}

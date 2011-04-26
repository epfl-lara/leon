#!/usr/bin/gawk -f
# ___  _  _ ____ ___ ___ ____ ___  ____ 
# |  \ |  | |     |   |  |__| |__] |___ 
# |__/ |__| |___  |   |  |  | |    |___ 
#
# The scripts were written to be usefull in
# a research enviornment, but anyone is welcome
# to use them.  Happy awking.  -Tim Sherwood

BEGIN {
	FS = " ";
	max_x =0;
	max_y =0;
}

{
	max_y++;
	for( i=1; i<=NF; i++ )
	{
		if (i>max_x) max_x=i;
		A[i,max_y] = $i;
	}
}

END {
	for ( x=1; x<=max_x; x++ )
	{
		for ( y=1; y<=max_y; y++ )
		{
			if ( (x,y) in A ) printf "%s",A[x,y];
			if ( y!=max_y ) printf " ";
		}
		printf "\n";
	}
}

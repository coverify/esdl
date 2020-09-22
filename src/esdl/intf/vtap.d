module esdl.intf.vtap;

version (Android) {}
 else
   {

     import core.sys.posix.unistd: sysread = read, syswrite = write, close;
     import core.sys.posix.sys.ioctl: ioctl, _IOW, SIOCGIFHWADDR;
     import core.sys.linux.fcntl: open, O_RDWR;
     import core.stdc.string: memset, strncpy, memcpy;
     public import esdl.posix.sys.net.if_;

     import std.bitmanip;

     class VirtualTap {
       enum BUFFERSIZE = 65535;
       int      _fd;
       string   _dev;
       int      _err;
       ubyte[6] _srcMAC;

       ubyte[] read() {
	 while(true) {
	   ubyte[BUFFERSIZE] buffer;
	   ubyte[] result;
	   size_t nread = sysread(_fd, cast(void*) buffer.ptr, buffer.length);
	   result.length = nread;
	   memcpy(result.ptr, buffer.ptr, nread);
	   return result;
	 }
       }

       void write(ubyte[] data) {
	 syswrite(_fd, cast(void*) data.ptr, data.length);
       }
  
       void write(byte[] data) {
	 syswrite(_fd, cast(void*) data.ptr, data.length);
       }
  
       void write(string data) {
	 syswrite(_fd, cast(void*) data.ptr, data.length);
       }
  
       this(string dev, short flags = IFF_TAP | IFF_NO_PI) {
	 ifreq ifr;
	 int fd, err;
	 string clonedev = "/dev/net/tun\0";

	 /* Arguments taken by the function:
	  *
	  * char *dev: the name of an interface (or '\0'). MUST have enough
	  *   space to hold the interface name if '\0' is passed
	  * int flags: interface flags (eg, IFF_TUN etc.)
	  */

	 /* open the clone device */
	 if( (fd = open(clonedev.ptr, O_RDWR)) < 0 ) {
	   _fd = fd;
	   return;
	 }

	 /* preparation of the struct ifr, of type "struct ifreq" */
	 memset(&ifr, 0, ifr.sizeof);

	 ifr.ifru_flags =  flags;   /* IFF_TUN or IFF_TAP, plus maybe IFF_NO_PI */

	 if (dev.length > 0) {
	   /* if a device name was specified, put it in the structure; otherwise,
	    * the kernel will try to allocate the "next" device of the
	    * specified type */
	   assert(dev.length < IFNAMSIZ);
	   strncpy(ifr.ifrn_name.ptr, dev.ptr, dev.length);
	 }

	 // TUNSETIFF = _IOW('T', 202, int) 
	 err = ioctl(fd, _IOW!int('T', 202), cast(void *) &ifr);
	 /* try to create the device */
	 if( err < 0 ) {
	   close(fd);
	   _err = err;
	   assert(false, "Error opening Vitual Tap: " ~ dev);
	 }

	 err = ioctl(fd, SIOCGIFHWADDR, cast(void *) &ifr);
	 if( err < 0 ) {
	   close(fd);
	   _err = err;
	   assert(false, "Error Getting SRCMAC address of Vitual Tap: " ~ dev);
	 }
	 memcpy(_srcMAC.ptr, ifr.ifru_hwaddr.sa_data.ptr, _srcMAC.length);
	 import std.stdio;
	 writeln("MAC address for ", dev, " is ", _srcMAC);
	 /* if the operation was successful, write back the name of the
	  * interface to the variable "dev", so the caller can know
	  * it. Note that the caller MUST reserve space in *dev (see calling
	  * code below) */
	 _dev = cast(string) ifr.ifrn_name;
	 // strcpy(dev, ifr.ifr_name);

	 /* this is the special file descriptor that the caller will use to talk
	  * with the virtual interface */
	 _fd = fd;
       }
     }

   }

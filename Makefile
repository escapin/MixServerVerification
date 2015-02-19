# java libraries: version
#BCPROV_t=jdk15on
#BCPROV_v=1.51
BCPROV_t=jdk16
BCPROV_v=1.46
JUNIT_v=4.12
HARMCRESTCORE_v=1.3



default: java_download java_compile 


java_download:
	-mkdir -p lib
	wget -P lib -nc http://central.maven.org/maven2/org/bouncycastle/bcprov-${BCPROV_t}/${BCPROV_v}/bcprov-${BCPROV_t}-${BCPROV_v}.jar

java_compile:
	-mkdir -p bin
	javac -sourcepath src \
          -classpath "lib/*" \
          -d bin \
          src/selectvoting/system/core/*.java    

java_clean:
	-rm -r bin